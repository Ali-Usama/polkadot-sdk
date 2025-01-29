import { readFileSync } from "fs";
import { getContract, parseAbi } from "viem";
import { wnd_ah } from "@polkadot-api/descriptors";
import { createClient } from "polkadot-api";
import { withPolkadotSdkCompat } from "polkadot-api/polkadot-sdk-compat";
import { getWsProvider } from "polkadot-api/ws-provider/web";
import { account, assert, walletClient } from "./utils";

const ahClient = createClient(withPolkadotSdkCompat(getWsProvider("ws://localhost:8000")));
const AHApi = ahClient.getTypedApi(wnd_ah);

const XcmExecuteAbi = parseAbi(["constructor()"]);
const hash = await walletClient.deployContract({
	abi: XcmExecuteAbi,
	bytecode: `0x${Buffer.from(readFileSync("pvm/XcmSend.polkavm")).toString("hex")}`,
});
const deployReceipt = await walletClient.waitForTransactionReceipt({ hash });
const rustContractAddress = deployReceipt.contractAddress;
console.log("Rust Contract deployed:", rustContractAddress); // 0x88bd3d3adac463964bc01378762ead5262932405
assert(rustContractAddress, "Contract address should be set");

const rawXcmBytes =
	"0x040100040c00040000000700e876481713000000017d000d00040000000700e8764817000101000101010101010101010101010101010101010101eeeeeeeeeeeeeeeeeeeeeeee"; // Sending funds on RC
// "0x05010005040603003448656c6c6f2c20576f726c6421"; // System.Remark

const estimatedGas = await walletClient.estimateGas({
	account,
	to: rustContractAddress,
	data: rawXcmBytes,
});
console.log("Estimated gas:", Number(estimatedGas));

const txHash = await walletClient.sendTransaction({
	to: rustContractAddress,
	data: rawXcmBytes,
});

const txReceipt = await walletClient.waitForTransactionReceipt({ hash: txHash });
console.log("Gas used:", Number(txReceipt.gasUsed));

const solidityContractAbi = [
	{
		inputs: [
			{
				internalType: "bytes",
				name: "_data",
				type: "bytes",
			},
			{
				internalType: "address",
				name: "rustLib",
				type: "address",
			},
		],
		name: "xcmSendRust",
		outputs: [
			{
				internalType: "bytes",
				name: "",
				type: "bytes",
			},
		],
		stateMutability: "nonpayable",
		type: "function",
	},
];
const solidityContractHash = await walletClient.deployContract({
	abi: solidityContractAbi,
	bytecode:
		"0x50564d0000442a000000000000010700c14000c000400480b20a000000000400000012000000200000002e0000003b0000004b0000005b000000660000007800000063616c6c63616c6c5f646174615f636f707963616c6c5f646174615f6c6f616463616c6c5f646174615f73697a657265665f74696d655f6c65667472657475726e5f646174615f636f707972657475726e5f646174615f73697a657365616c5f72657475726e7365745f696d6d757461626c655f6461746176616c75655f7472616e73666572726564051102a4230463616c6ca42b066465706c6f7906a9625002a437ce00e700ec000b017601b101e001fc010e022802a002a402b902fc021203f8033a0465048e04a004db043505d7055c0690064808f1089609c109ea09010a130a360b730b890ba00d6b0e860ea60ec10ed70e140faf10c81135145314a21418152a167b169f16f916bf172d1843185918ae1827195919631a8e1ab71ac91a061b651b0e1cc41c641d731ecc1e771fe51ff81f652033234123b823f2232b24342464798b7a103307520a41330a000001ac8a39c8980883871f8477e054370000010a330732003908000002ae78143d0700000264783307200002c8870732003307200002c8870732003200aa876e978a2098aa20977b2098bb20c89b0bc9ba0a979b019abbaeab20ae873751094ec87909647a017c8b95880195ac0178ab64caab9cf42836510934c87909647a017c8b95880195ac0178ab64caab9cf4281c51091a839aff01c8a80b7cbb9599ffc8a70c78cb83aaff5209f032009511f07b10087b158475013307330850100237ff3e070800020a03013e071000023b052000035105075010040950100627019511c07b10387b15307b16289515408411e06416330740330820501008fafe5107f4003308080002210358000221035000022103480002140700000000000000807b68103e076000029517e08477e07b67186471491718491710491708490783770a0901826a1882a71082a81882a90882aad49808d4a707d4870752078c0033074033082050100a8ffe51078900826a1082a74882a85882a94082aa506f7b6f87d4b708d4a9096f99d49808988820d4b909979920d4980852085b83777b671850100c54fe51074e826710826818be8707330833090a0101390814000251080d330740000383770a0801826718330850100e25fe51071f826710826818be7808330733090a07013307330850101009fe5207040081681033070133093300120a07019511c07b10387b15309515408411e0330740330820501014ddfd52070400210358000221035000023908100002140900000000000000803e09600002210348000254180351831733080a020180171c977720140800000000ac0a8aaaab8736330016951120fe7b10d8017b15d0017b16c8019515e0018411e04921b8014921b0014921a8014921a0018317a0010a092839135010184e9511f07b10087b15647533074033082050101a4cfd5107343a086000023a095800023a0a5000023a074800026f886f996faa6f777b57187b5a107b59087b5882100882159511103200009511f87b103307330850101c09fd5207040033080800028388330701330933001e0a07018289828218828b08828810959c1fd89c09c89b0ad8ba0bda990bc88b0bd88b08c8280884cce07b7c7b7a087b7b107b781832009511d87b10207b15187b16108273188274108279088270828c828218828508828a1095c61fd8c60bc8b507d85705dabb05c85a08d8a80a8466e07b1008c86000d86006c8970bc86b0cd37c0bd87c05dab605c8480bc8b505d8b506d88b07c83202c8a208c88707c876068e678e58db6708d465078ecbdb780b520b72821708d87007d39c08d89c09da8709d84507d33608d8360ada870ad34507d48707da790a520a4b7b1c7b10083307403308205010200dfc510799006f6733080800026f59821a6faa821b086fbb3e0b6000023e0a5800023e095000023e0748000282102082151882161095112832003308203307501022cbfb510757330508000221032000022103180002210310000221030800024e487b71330704330820501024a0fb51072c4815200000004148151c48151848151448151048150c481508481504330824330750102677fb5207040083583307013309243300280a0701951160ff7b1098007b1590007b1688009515a0008411f08289187b19388289107b19208289087b192882887b1830647633074033082050102a2afb510786003a086000023a095800023a0a5000023a074800026f887b18186f997b19106faa7b1a086f7b7b1b8217207b17508217287b17488217307b17407b1b787b1a707b19687b18609517609518408219387b195850102c15fe82177b67188217087b67108217107b67088217187b67955160ff8210980082159000821688009511a000320000951100ff7b10f8007b15f0007b16e800951500018411f0829c18829b108296087b1b507b1c48d4cb0b7b169800886c0194bc510cf8037b170882a7187b172882a7107b173082a7087b171882a77b172082968287187b17608287107b17388287087b175882877b17800033074033082050102e2efa51072d0495671f7b1640d8670882199800c898088488018479e0959220d8920a3307080002c8a80bd88b09daaa093a086000023a0a5800023a0c5000027b17703a074800026f887b18786faa7b1a90006fc66f777b1788004921b8007b17d8007b16d0007b1ac8007b18c0007b12a0007b1ba8009517c0009518a0007b19b000501030eefc8219788218880082179000d48707d46908d478089888207b1668d46707977720d487075207850383973308207b171050103275f95107740382124082178000c82707d82709821c9800821858c8c808c8980ad3ca0bd8ca08dab908821b18d3ba09d8ab0a821b20d87b07821450821038c8040bdb9a07d84b09821348821a60c83a0ac8a909c8b808d8b80ac8a909821b28d3b90ad89b09821630d8860bdaab09d36808d4a808821a70821610c8a606db89076f2898893878691f98893078691e98892878691d98892078691c98891878691b98891078691a6fc97868189888087868199898387868179898307868169898287868159898207868149898187868139898107868126f4878691098990878691198893878690f98893078690e98892878690d98892078690c98891878690b98891078690a6f39786808988808786809989838786807989830786806989828786805989820786804989818786803989810786802786998990878690152072f0282178000d40707821858821960d49808d48707987720d40808978820d4870782167852071502d4420782189800d43808d48707987720d44808978820d487075207f80182176882188800d487071408e0ffffff00000000d8860882199000949894785108d50195672083287b176083777b17387b1858501034bdf75107bc01821760d8670782189000c87806d88608da7708821768c878087b1830d878077b172881198000821770821838be87078218580a0101821240821860c82807d8870882199800c86909c88909d3690ad8690bdaa80b82188800821a48c8a808821a28c8a808821a50821c30c8ca0ad8ca0cc8c808c8ab0bd8ab0ac8a808d49808d4b707d48707d4b808987720978820d4870752072701821660be2606330820646750103614f751071301821770c8760646161f46161e46161d46161c46161b46161a46161946161846161746161646161546161446161346161246161146161046160f46160e46160d46160c46160b46160a46160946160846160746160646160546160446160346160246160146068217088218787b78821888007b7818821890007b78088218687b7810955100ff8210f8008215f0008216e80095110001320033082033075010386ff651076e330608000221032000022103180002210310000221030800024e487b7133070433082050103a44f65107434816200000004148161c48161848161448161048160c481608481604330824330750103c1bf651071a83683307013309240a07013307330850103e04f65207040081187033070133093300400a0701951100ff7b10f8007b15f0007b16e800951500018411e08280829b088284088296950a1fd80a03c8340c7b1620d86a0ad3bc067b1b28d8bc0bda6a0b8282107b1438d84c0ada330a829318828c18829610c82a0ad82a087b1c30c8c808d33809d93808d86a0cda9c08d36a0ad4a909db980b510be50064247b16087b13107b1718d44007821838821930d49808d48707987720d44808978820d487075207c700644683088317c0007b100a028212c0008213c8008219d000821ad8008217957b20d87b0c821838c8c807d88708dacc08c86808d8680c821630c86c0c8216107b16588216087b16508216287b16488216207b16407b1a787b19707b13687b12607b1788007b1b80007b1890009517a00095188000951960951a407b1c980050104231fa8217b0008218b8008219a000821aa800821b187bb7107bb8187bb97bba08955100ff8210f8008215f0008216e8009511000132003307330850104492f4520704003308080002838833070133093300460a0701808910828a0882884917187b79107b7a087b7832009511a0fe7b1058017b1550017b164801951560018411e0829608828208829c8283829010d3260bd8260ad83c04dab40a7b1678c9260bc94b0b7b1c70c93c0c88cc4085cc018284108eb6dbb60c829b18828618c94008c9a809d8a8087b1068d8400a7b1b60c96b0bc9ab0bc98b0b8fb88e9adbb80ad4b909db9a0c510c4902d443097b1258d46208d489099899207b1450d44808978820d4980852088c027b16487b17308338831700017b183864360a02018217180182181001821908018e7a8e8bdb7a0bd4780a8e9cdbab0c520c1202821a0001c86a02d8a20a821b58c89b0bc8ab03d3930b7b1640d89306daba06821950c88909c89606d8960ad88908821948c89707c88707c8a70095271fd82708c88309d8390ada880ac8a604d86408c80808821c78d3c90bd8c909821c70d8c707dbb907821c68d8c409821b60d3b80ad9b808daa908d3c409d4a909db98075107b101d462077b13287b1018d40308d487079877207b1620d46808978820d487075207b40183288317200164260a02821220018213280182193001821a3801956b20d86b0c821828c8c807d88708dacc08821c20c8c808d8c80c821618c86c0c8216607b1698008216687b1690008216787b1688008216707b1680007b1ab8007b19b0007b13a8007b12a0007b17c8007b1bc0007b18d0009517e0009518c0009519a000951a80007b1cd800501048c7f7821b508eb7821c488ec8dac708140600000000010000001407dfffffff00000000821940d89707821a588ea9daa709d4cb07db78095209ef008217f8007b17788217f0007b17708217e8007b17608217e0007b1768821738837820831720010a02018218300182173801d38606d476069889208899019479936951099e0082192801821a2001821b307bb9287bba208219607bb9088219687bb97bb8308218707bb8107bb7388217787bb7189551a0fe8210580182155001821648019511600132003307330850104a9af15107593308080002838833070133090a07013307330850104c7ff151073e3308080002838833070133090a07330833004e2864f1330850104e5ff151071e3308080002838833070133090a07013307330850105044f1520704003308080002838833070133093300520a07019511e87b10107b15087b16828910828a18828b088286d4ba0ad49608d4a808988820d4a909979920d4980852084501647583663308206467501054f1f0510733013307080002c876067c67017c687c69027c6a03977708d4870797991097aa18d4a909d497077c68057c69047c6a067c6b07978808d4980897aa1097bb18d4ba0ad4a808978820d478027c68097c69087c6a0a7c6b0b978808d4980897aa1097bb18d4ba0ad4a8087c690d7c6a0c7c6b0e7c6c0f979908d4a90997bb1097cc18d4cb0bd4b909979920d498087c69117c6a107c6b127c6c13979908d4a90997bb1097cc18d4cb0bd4b9097c6a157c6b147c6c167c671797aa08d4ba0a97cc10977718d4c707d4a707977720d479097c67197c6a187c6b1a7c6c1b977708d4a70797bb1097cc18d4cb0bd4b7077c6a1d7c6b1c7c6c1e7c661f97aa08d4ba0a97cc10976618d46c0cd4ca0a97aa20d4a7076f776f996f886f2a7b5a187b58107b59087b578210108215088216951118320000951190fe7b1068017b1560017b165801828b10828618828a08828c7b1a20017b161001d46a08d4bc0ad48a0a98aa207b1b1801d4b808978820d4a8087b1752084f058297187b17500182961082950882977b1740017b1c080183c73308207b17380150105656ef5107260582194001d469077b15280182185001d45808d487079877207b163001d46808978820d487075207fd043308080002821738017b184801c887077c78187b18287c78197b18087c781a7b18187c781b7b18107c781c7b18407c781d7b18207c781e7b18387c781f7b18307c78107b18687c78117b18487c78127b18587c78137b18507c76147c78157b18607c78167b18787c78177b18707c78087b18a0007c78097b1880007c780a7b1890007c780b7b1888007c780c7b18b8007c780d7b1898007c780e7b18b0007c780f7b18a8007c787b18e0007c78017b18c0007c78027b18d0007c78037b18c8007c78047b18f8007c78057b18d8007c78067b18f0007c77077b17e80083973308207b17000164955010583dee51070d04821b30018eb7821c50018ec9dac7091408dfffffff00000000d8580a821728018e78da7a08d4cb0adba908821908979908821728d47909821a1897aa10821b1097bb18d4ba0ad4a909821a2097aa08821740d47a0a821b3897bb10821c3097cc18d4cb0bd4ba0a97aa20d4a909821a4897aa08821768d47a0a821b5897bb10821c5097cc18d4cb0bd4ba0a821b6097bb08d46b0b821c7897cc10821670976618d46c0cd4cb0b97bb20d4ba0a821b800097bb088217a000d47b0b821c900097cc1082168800976618d46c0cd4cb0b821c980097cc088217b800d47c0c8216b00097661064538215a800975518d46505d45c0c97cc20d4cb0b821cc00097cc088217e000d47c0c8216d0009766108215c800975518d46505d45c0c8216d8009766088217f800d476068215f0009755108217e800977718d45707d46707977720d47c0c8215480182170001c8750598c73878570798c73078570698c72878570598c72078570498c71878570398c71078570298c70878570198b73878570f98b73078570e98b72878570d98b72078570c98b71878570b98b71078570a98b70878570998a73878571798a73078571698a72878571598a72078571498a71878571398a71078571298a70878571198973878571f98973078571e98972878571d98972078571c98971878571b98971078571a989708785719785b08785c785a10785918520809028217180182181001d487071402e0ffffff0000000082180801d8280882162001946894785108e1016fc66fbb6fa86f99d4b9077b181801d46808d487079877207b1b2001d4b808978820d487075207b8018337207b19100183957b170801645850105ad0eb5107a0017b160001821738018377207b17f8007b153801645850105cb2eb5107820182174001957520d8750782182801c87806d88608da770882173001c878087b184001d8780782185001c887077b1750018218480182170801c887078219f800c898088219380150105eadeb821a10017b153801c85a07d8a7087b163001821b1801c86b09c88909d3b90cd8b90bdac80b821c200182184001c8c808c88b0bd88b06d8c808821c000182155001c85c0cc8c808c86808d4b707d49808d48707987720d4b808978820d487075207d40082153801bea505330820645764a6501060edea5107bd0082174801c8750546151f46151e46151d46151c46151b46151a46151946151846151746151646151546151446151346151246151146151046150f46150e46150d46150c46150b46150a461509461508461507461506461505461504461503461502461501460595671f1408e0ffffff01000000d2870782183801c87808d8780782193001c879099497821a4001c8a707d8a70a821b5001c8ba0a821b7bb87bb9087bb7107bba18821068018215600182165801951170013200008217b0018218b8018219a801821aa001d49808d4a707d4870752074b0238071000024921380149213001492128017b172001492158014921500149214001049517600195184001951920014921480150106279f582126001821768018218700182197801821b8001821c880182169001821a98017b1ad8007b16d0007b1cc8007b1bc0007b19f8007b18f0007b17e800951700019518e0009519c0007b12e0005010648209821718017b1748821710017b1750821708017b17588216000133074033082050106666e95107a7017b164033060800023a075000023a084800023a095800023a0a6000026f7c6f826f9b6fa9d42b07d4c908d47808988820d4c707977720d4870752076a017b12207b1c287b1b307b193883973308207b17185010680ce951074d01821838958720d88708821a30c88a09d8a90ada880a821b28c8ab08d8b80a821b20c8ba0a821b18c8b60646161f2046161e46161d46161c46161b46161a46161946161846161746161646161546161446161346161246161146161046160f46160e46160d46160c46160b46160a46160946160846160746160646160546160446160346160246160146067b19687b17608217487b1798008217507b1790008217587b1788008217407b1780007b18709517a000951880009519607b1a7850106a8ef88218a8008212b8008213a000821ab000821730d3780bd8780c6470821438d84309dab90c821728c97a0bd87a0a821720c97207c9a707d8cb0ac9a707c9cb0bc90808c99808d48707c94308d4b808d47808d4b707988820977720d4870752072abf43088217187b185850106cd8e7510719836833078219580a07013307330850106ec2e7520704003308080002838833070133093300700a07014917184917104917083308607b783200951150ff7b10a8007b15a0007b1698009515b0008411f0828a18828910828b087b19287b1a20d4a9097b1b4088ba01949a510abf017b1718828633074033082050107257e751070c0295671f7b1608d86708821940c898088488018479e0959220d8920a3307080002c8a80bd88b09daaa093a086000023a0a5800023a0c5000027b173a074800026f887b18486faa7b1a386fc66f777b17304911687b1788007b1680007b1a787b18707b12507b1b589517709518507b196050107423ea821830821738d48707821848d46808d478089888207b1610d46707977720d48707520772018116483308206467501076ace6510761018217c876068217206f778218286f888219406f99821a086faa786a1898ab38786b1f98ab30786b1e98ab28786b1d98ab20786b1c98ab18786b1b98ab10786b1a98aa08786a19786910989a38786a17989a30786a16989a28786a15989a20786a14989a18786a13989a10786a1298990878691178680898893878690f98893078690e98892878690d98892078690c98891878690b98891078690a98880878680978679878387868079878307868069878287868059878207868049878187868039878107868029877087867018217188218487b788218307b78188218387b78088218107b7810955150ff8210a8008215a000821698009511b00032003308203307501078a2e5510757330608000221032000022103180002210310000221030800024e487b7133070433082050107a77e551072c4816200000004148161c48161848161448161048160c481608481604330824330750107c4ee552070400836833070133092433007e0a0701951160ff7b1098007b1590007b1688009515a0008411e064760a06015107b5007b16200a064911584911507b17409517609518404911485020800069fd8216788217707b17388217687b17308217607b17280a0601821b288e68821c388ec9db68091408dfffffff00000000d8b8028218308e8ada820a7b1618d46c08db890a520a50647698772052074883b72083687b17087b181050208200a1e45107343307080002821808be87077a1680008318800033090a050181178000821620821818821938821a30821b28821c10aec70e00330a33093308330b60017b6b7b6a087b69107b6818955160ff8210980082159000821688009511a00032009511a07b10587b15507b1648828b10828918828a0882857b19307b1a40d49a08d4b509d489099899207b1b38d4b808978820d498087b1718520827028357330820647650208400f8e35107160233070800027b1720646cc8670746171f2046171e46171d46171c46171b46171a46171946171846171746171646171546171446171346171246171146171046170f46170e46170d46170c46170b46170a4617094617084617074617064617054617044617034617024617018219388e98821a308ea6daa8061408dfffffff000000007b1528d85808821b408eb57b1510dbb508d4a9097b1908db96084607520874017b1c83c52033082064575020860042e351076001821720c8750546151f1b46151e46151d46151c46151b46151a46151946151846151746151646151546151446151346151246151146151046150f46150e46150d46150c46150b46150a4615094615084615074615064615054615044615034615024615011407bfffffff00000000821828d88707821840821910db8907821808db860746055207d7008217837640330820330520646750208800a2e25107c000821720c87606461617724616156e46161068461619634616136346160a634616146f4616086f46161a744616167446160f744616077446161f46161e46161d46161c46161b78651278650e78650978650646160564461611654616046546160d6c46160c6c4616036c461602694616186146160b6146160161460646821828958760d88708821a40c88a09d8a90ada880a821838c88a0ad88a08821b30c8b808821b187bb77bb9087bba107bb818821058821550821648951160320000951170ff7b1088007b1580007b1678951590008411f0827810827918827a088277d4a909d48707d49707510718955170ff821088008215800082167895119000320033074033082050208a0093e15107750133060800023a075000023a084800023a095800023a0a6000026f7b6f8c6f976fa87b17207b1c10d4c7077b1828d4b808d478089888207b1b18d4b707977720d4870752072f018117283308207b170850208c003ae151071c01821708c8760646161f46161e46161d46161c46161b46161a46161946161846161746161646161546161446161346161246161146161046160f46160e46160d46160c46160b46160a461609461608461607461606461605461604461603a00046160279461601c300460608821828958704d88708821a20c88a09d8a90ada880a821818c88a0ad88a08821b10c88b0b7b19387b17307b1a409517509518307b1b4850208e0054fc821858821268821350821a60821720d3780bd8780c6470821428d84309dab90c821718c97a0bd87a0a821710c97207c9a707d8cb0ac9a707c9cb0bc90808c99808d48707c94308d4b808d47808d4b707988820977720d48707520718821728bf73088217087b18285020900021e0520704008368330701821928330092000a0701951180fd7b1078027b1570027b166802951580028411e0828a18828b10828c0882867b1a58017b1c4801d4ac08d4b60ad48a0a98aa207b1b5001d4b808978820d4a8087b17205208e4038297107b1738018297087b17300182977b17400183673308207b17280150209400a1df5107bd039567207b171801d867083309080002821a4801c88a077b172001d8a707da88077b191882182801c898087c89187b19487c89197b19287c891a7b19387c891b7b19307c891c7b19607c891d7b19407c891e7b19587c891f7b19507c89107b1988007c89117b19687c89127b19787c89137b19707c89147b19a0007c89157b1980007c89167b1998007c89177b1990007c89087b19c8007c89097b19a8007c890a7b19b8007c890b7b19b0007c890c7b19e0007c890d7b19c0007c890e7b19d8007c890f7b19d0007c897b1908017c89017b19e8007c89027b19f8007c89037b19f0007c89047b1948017c89057b1900017c89067b1928017c88077b18100182185001c87806d8860782185801c887077b1758010a040182121801821730016f77977820821938016f99989920d49808821940016f99979a20987720d4a7079899207b17a8017a19b0017b18a0014921d8014921d0014921c801d462078218200182195801d49808d48707987720d46808978820d487074921c00152073f02821728977708821848d48707821838978810821930979918d49808d48707821840978808821960d49808821958979910821a5097aa18d4a909d49808978820d4870782186897880882198800d49808821978979910821a7097aa18d4a909d4980882198000979908821aa000d4a909821a980097aa10821b900097bb18d4ba0ad4a909979920d498088219a800979908821ac800d4a909821ab80097aa10821bb00097bb18d4ba0ad4a909821ac00097aa08821be000d4ba0a821bd80097bb10821cd00097cc18d4cb0bd4ba0a97aa20d4a909821ae80097aa08821b0801d4ba0a821bf80097bb10821cf00097cc18d4cb0bd4ba0a821b000197bb08821c4801d4cb0b821c280197cc1082161001976618d46c0cd4cb0b97bb20d4ba0a6f996f77d4a808d4970a6f88d48a0ad4980898aa20978820d4a808520803018326837864677b18580150209600d3dc5107ef003307330850209800c5dc5107e100821918c896064821e00149211802ff49211002ff49210802ff49210002ff48212002089518a0017b18240249213002ff49212802ff951700027b1738029517c0017b173c027b164002821758017a1744027b1948029517e0017b174c02831720020a8877017b1748019517800150209a0017f7821780017b175801821788017b175001821790017b174001821698014921780149217001821748017b176001951760014921680150209c0039fa8217207b7618821840017b7810821850017b7808821858017b78955180fd82107802821570028216680295118002320000330750209e0095dc3307015020a0008cdc28badea58424092a2414524825499294242da994b4a45232252525a542680889902449498810420820214949aa495292484224492a2949921292a41a126a0a4952ad9049699224091942082084a826012411119188882891541212420855494a69aa90a19496244992242529499254922449922449922449924a4a9224499224250951a8520821244929248410022421812449924296a411119124494a4988104228a5549224499224a124498a8888464444922489144992a494244991844812499290248490508a8a88888888889088244992280991482249922449922449922449922449499224495292244992242949922449929424499224494a229224499248244912890490a848290991449224492449932492249124499224499224921422499224499224499224499224254522494444944242082140121248922429a4a41532298d88889494244992244992244992244a92244992a8a888889224499224499224898888244244449212111155c8504a939254444424a92449922449499224495249224992249114a9115149894892244992244992244992244992244924499224515444449224499244229188888888888808292580009294242291482489462449454492242549121111554828b54242a9924242a9153294d2242529499244a51021294992244992244992244992244992244992244992244992244992244992244992aa2425a51111498a489248522492224a8488442489241122922449922449922449922449128944229148248a442291482412250a1145092051922449922449922449922449922449922491482492442291224912894422492412892449449224499224499224499224499224499224499224495212110920121555892491241245212212518848224924128988442244241149928824894892244922920a1149922449922449922449922425804412299248258988684444920811111121222244444444444444444444884422918448082184aa2449124952122249922449924892244992244992244992a42491482412918488882425499224499224499224219556c8504a93a4222222499224454a4224499224240921144aa92422499284244992249114a2a4945292244992244992244992244992244992a424499224499292248988885248082104484202499224852c4923222235529224419224694a09202949529292202189a8912449565992888828499294244992244a418494489224499224499224499224a50490a4244951521049244992244992244992244912409224294a521049444444444444922449222222222292244992242949923422124952924444a22488104208554992244922491049922449922449922449928408499224499224498224495292244992244992244992204ba2111191244524492449241245892012099148124992244992244924499248241289442291482412452291482412894822d188122551924444442422499288244992244992244992489224914824922491482492442291489244229148128944224952494992a822880a228910420811214444444444c44404111111111111112491481411112d481000",
});
const deployReceiptSolidity = await walletClient.waitForTransactionReceipt({
	hash: solidityContractHash,
});
const solidityContractAddress = deployReceiptSolidity.contractAddress;
console.log("Solidity Contract deployed:", solidityContractAddress);

const solidityContract = getContract({
	address: solidityContractAddress!,
	abi: solidityContractAbi,
	client: walletClient,
});
const resultSolidityCrossContractCall = await solidityContract.write.xcmSendRust([
	rawXcmBytes,
	rustContractAddress,
]);
console.log("Result Cross Contract Call:", resultSolidityCrossContractCall);
