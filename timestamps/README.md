# Timestamp proof for v1.0.0

`kyle-uniqueness-lean-v1.0.0.commit` contains the commit hash of tag `v1.0.0`
(`11f88ae3a0c1991d15b9bf830964ce8bb82a9136`, the complete, 0-`sorry`
formalization). `kyle-uniqueness-lean-v1.0.0.commit.ots` is an
[OpenTimestamps](https://opentimestamps.org) proof that this file existed by
2026-11-03, anchored in Bitcoin block 974376.

To check it yourself:

```bash
git rev-parse 'v1.0.0^{commit}'          # must print the hash above
ots verify timestamps/kyle-uniqueness-lean-v1.0.0.commit.ots
```

`ots verify` needs a Bitcoin node or a block explorer to confirm the block
header; `ots info` prints the full attestation path without one.
