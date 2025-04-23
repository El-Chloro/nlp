.PHONY: pcfg_tool
pcfg_tool:
	cargo build --release
	cp -p target/release/nlp ./pcfg_tool