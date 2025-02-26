echo "✅ building chain-spec-builder and ah-next-runtime"

LOG="runtime::multiblock-election=info,runtime::staking=info"

RUST_LOG=${LOG} cargo build --release -p asset-hub-next-westend-runtime -p staging-chain-spec-builder

echo "✅ creating chain spec"
RUST_LOG=${LOG} ../../../../../target/release/chain-spec-builder \
    create \
    --runtime ../../../../../target/release/wbuild/asset-hub-next-westend-runtime/asset_hub_next_westend_runtime.compact.compressed.wasm \
    --relay-chain rococo-local \
    --para-id 1100 \
    named-preset genesis

# ensure local file `chain_spec` is created in current directory
if [ ! -f chain_spec.json ]; then
    echo "chain spec not created"
    exit 1
fi

echo "✅ launching ZN"
zombienet --provider native -l text spawn zombienet-omni-node.toml
