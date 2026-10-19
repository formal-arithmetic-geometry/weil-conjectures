# Worker report

Files written:

- `dag/nodes/sec-trace-formula/lem-trf-proper-fibrewise-ample-projective.json` — repaired item, split; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-fibre-degree-ample-criterion.json` — existing statement-only node, no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-ample-neighbourhood.json` — existing statement-only node, no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-relative-ample-very-ample.json` — existing statement-only node, no Mathlib match; source corrected to Tags 01VR/01VU.
- `dag/nodes/sec-trace-formula/lem-trf-projective-bundle-separated.json` — new statement-only node, no Mathlib match; Stacks Tag 01OD.

Attachments: none. No sorry-free declaration in the source states the item.

WANTED: none.

The returned review found four issues: the Noetherianity of geometric fibres was asserted without a cited finite-type-over-Noetherian result; descent from geometric to ordinary fibres was omitted; affine polynomial projective-space separatedness was applied to a general relative projective bundle; and the evaluation-immersion clause was attributed to Tag 01VU instead of Tag 01VR. I repaired each point. Step 1 now cites `lem-weil-pbc-finite-type-over-noetherian`; Step 2 explicitly descends ampleness along the faithfully flat algebraic-closure extension using `lem-pc-very-ample-descends`; Step 5 cites the new relative projective-bundle separatedness node; and the relative very-ampleness source fields cite 01VR and 01VU correctly.

## Not duplicates

- `lem-trf-projective-bundle-separated` vs `lem-weil-pbc-projective-space-proj-separated`: the new node covers an arbitrary relative projective bundle over any scheme (Tag 01OD), while the existing node covers only polynomial projective space over an affine base.
- `lem-trf-relative-ample-very-ample` vs `def-sc-ample`: the new node is relative over a base and includes the evaluation immersion; `def-sc-ample` is the absolute field notion.
- `lem-trf-relative-ample-very-ample` vs `lem-trf-proper-fibrewise-ample-projective`: the new node is the relative ampleness/very-ampleness equivalence and evaluation clause used by Step 4, while the item proves the fibre-degree criterion and projective conclusion.
- `lem-trf-ample-neighbourhood` vs `lem-trf-proper-fibrewise-ample-projective`: one is a local neighbourhood theorem for a single fibre; the other is the global fibre-degree/projectivity criterion.
- `lem-trf-fibre-degree-ample-criterion` vs `lem-pc-ample-positive-degree`: the new criterion allows arbitrary proper Noetherian dimension-at-most-one schemes and all normalized components; the existing node concerns smooth projective curves over a field.
- `lem-trf-fibre-degree-ample-criterion` vs `lem-trf-proper-fibrewise-ample-projective`: the new node is the absolute one-fibre degree criterion used in Step 2, while the item is the relative morphism theorem with neighbourhood and projective-bundle conclusions.

## Review by Q85

I reread the repaired item and all four auxiliary nodes, every cited statement, and the Stacks passages for Tags 01T6, 0B5Y, 0D2S, 01VR, 01VU, 01OD, and 02O5. Step 1 checks properness gives finite type, the geometric fibre is a base change, and finite type over the Noetherian algebraically closed residue field gives a Noetherian fibre via 01T6. Step 2 checks both fields in the geometric/ordinary fibre comparison and records the faithfully flat ampleness descent before invoking the neighbourhood theorem. Step 3 applies that theorem to ordinary fibres and uses quasi-compactness for a finite affine cover. Step 4 uses 01VU for a common tensor power and 01VR for relative very ampleness. Step 5 uses proper coherent pushforward, the 01VR evaluation-surjection/immersion clause, and the new 01OD separatedness statement before properness makes the immersion closed. I regenerated `citations.json` from exact node statements and verified the old polynomial-projective-space node is absent from the proof dependencies. Edge cases checked were a point, empty and zero-dimensional fibres, and a reducible curve with a degree-zero component.
