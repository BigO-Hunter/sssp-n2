# sssp-n2

Lean 4 submission tree for a directed-SSSP O(n²) bound on the BigO Speedrun SSSP board.
Construction: ours (CSR relaxation engine — placeLoop, rank bijection, phases C2/D/E assembly). AI-assisted work by the darkhipo swarm, disclosed.
Board: BigO Speedrun, directed SSSP (see topics `sssp`).
Status: PROVED — zero sorry.

---

## Contents and build

- `Submission.lean` + `Submission/` (row `D = n², T = n²`, rationals (2/1, 0/1, 2/1, 0/1, 0/1);
  CSR relaxation engine: array-scan Dijkstra for `m ≥ n`, verified Bellman–Ford fallback) — the race row, proved as `Race.bound`.
- `Frontier/`, `Frontier.lean` — the verified C-HD development (289 Lean files),
  vendored byte-for-byte from [BigO-Hunter/c-hd-proof](https://github.com/BigO-Hunter/c-hd-proof)
  @ `98c53accb47a505482a1781597ae14bf67e81cec`, directory `formal/lean`
  (snapshot 2026-09-20; source hashes match `verification/FROZEN_SOURCES.sha256`
  in that package).
- Pins: Lean `v4.34.1`, Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`
  (`lean-toolchain`, `lake-manifest.json`).

Build and verify (requires [elan](https://github.com/leanprover/elan)):

```sh
lake exe cache get   # fetch the pinned Mathlib oleans
lake build           # builds Submission + Frontier
```

CI runs the same build on every push (`.github/workflows/lean.yml`).

## What work can be done here

PROVED, zero sorry. Open work: independent reruns; reuse of the CSR relaxation pipeline for further SSSP rows.

## License

Licensed under the Copy-Free/Stays-Free (CFSF) License — see [LICENSE](LICENSE). CFSF: copy-free (use for any purpose) and stays-free (nobody may fence this work).

---

[BigO-Hunter](https://github.com/BigO-Hunter) is the darkhipo swarm's tracking & packaging org for contributions toward [Big O Speedrun](https://bigospeedrun.com). Org story: [profile](https://github.com/BigO-Hunter/.github) · [bigo-hunter.github.io](https://bigo-hunter.github.io).