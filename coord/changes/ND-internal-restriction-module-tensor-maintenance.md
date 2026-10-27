# ND internal-restriction stage-2 maintenance, 2026-10-24

The returned consumer delivery at 56c17f3d1baf was required to extract existing
internal-action definitions unchanged and cite a definition owner (H2), and to
pin its comparison isomorphisms on sections (H3). The retained H2/H3 worker repair
compiled, but repeated dry runs rejected the published
`restrictLinearAction_naturality` proof after it moved to a new module.
`tools/stage2_delivery.py:check_lean_text` exempts published proofs only against
the same file on the base; the extracted file has no base text. The return's
`existing:true` shape therefore requires a preceding library extraction.

This maintenance change performs that extraction with no new mathematics:

- `InternalActionInflation` owns `restrictLinearAction_naturality`,
  `restrictLinearAction`, `inflateSheaf`, `ActionForgetExact`, and
  `trivialSheafAction`. Their signatures and bodies are literal transfers;
  only blueprint ownership tags change.
- Both original theorem modules publicly re-export the new module and retain
  every other declaration and proof unchanged.
- The new definition node records the landed declarations with `existing:true`.
  The two theorem nodes cite this owner and no longer claim the extracted names.

Backups of every affected path are retained alongside the path with the suffix
`.maint-ND-internal-restriction-1792843705.bak`; a new path has an empty backup
recording its previous absence. No launcher, preflight, review or landing tool
is changed. The consumer theorem is left for its normal stage-2 delivery/review.

Validation: literal extraction comparison passed; compile the three library
files separately with `tools/lean_file.sh` under the default 60-second limit
before committing. The maintenance command aborts without a commit if any fails.
