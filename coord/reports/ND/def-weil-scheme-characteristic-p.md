## Worker report

Files written:

- `dag/nodes/sec-smooth-purity/def-weil-scheme-characteristic-p.json`: the repaired stage-1 split, now carrying the stage-2 `lean` record for the delivered declaration.
- `lean/Sheaf/Paper/SchemeCharacteristicP.lean`: the stage-2 definition module.
- `citations.json`: `[]`, because the item is a definition with no proof steps.
- `report.md`.

New nodes: none. New Mathlib leaves: none.

Attachments: none. `AlgebraicGeometry.Scheme.overSpecZModOfCharP` in
`/home/ubuntu/weil-src-slopmaster2/WeilConjectures/FourierTransform/ArtinSchreier.lean:496`
assumes a ring-level `CharP` instance and constructs a morphism to `Spec (ZMod p)`; it does
not define this scheme-level predicate, so it is not an attachment.

WANTED: none.

The imported stage-1 statement had added global-section, stalk, and factorization equivalences
that were not in the Stacks source. The repaired node keeps the source-faithful condition that
`p` is zero in every structure-sheaf section ring. Its statement dependencies are the existing
scheme and locally-ringed-space notions; no separate theorem node is needed for a definition.
The stage-2 return also required the actual Lean declaration, its complete record, a clause-by-clause
Lean reading, and compilation evidence; those are supplied below.

## Review by ND

I read `coord/brief-stage1.md`, `stages/1-dag.md`, `SETUP.md`, `GOAL.md`, `coord/dag-sync.md`,
and delivery-errors B-E before editing. I read the item, its chapter record, the ancestor
`def-weil-frobenius-detailed`, the Stacks source at
`literature/stacks-project/varieties.tex:7010-7018` (Section 33.36, tag 0CC6), and the existing
nodes `def-pc-scheme` and `def-weil-locally-ringed-space-morphism`. The item is not a unit key
node, so no unit record changes.

The source has exactly two clauses: `p` is prime, and `X` has characteristic `p` when `p` is
zero in its structure sheaf. The Lean declaration records these as `_hp : p.Prime` and
`∀ U : X.Opens, (p : Γ(X, U)) = 0`. The empty scheme satisfies the condition vacuously. The
zero ring and an affine `Spec A` with `p · 1 = 0` pass; `Spec ℤ` at a prime p does not.
The imported global/stalk/factorization package was therefore removed from the source-faithful
statement. No proof fact is hidden in the definition, so `proof`, `proof_deps`, and
`citations.json` are empty.

I searched the complete DAG and blueprint for the predicate and its source tag, and searched
Mathlib and the two read-only project checkouts for exact declarations. Mathlib supplies the
ring-level `CharP` class and `AlgebraicGeometry.Scheme`, but no predicate on schemes. The
related `overSpecZModOfCharP` declaration was read and rejected as non-exact. The recorded
Mathlib searches were run with `msearch.py`; LeanSearch was unavailable and is recorded as
unavailable in the node.

Against delivery-errors B-E, I checked every statement dependency against its node, ruled out
new theorem nodes and duplicates, and verified that the definition introduces all objects it
uses. The module has no local notation, private declarations, hollow data, or `sorry`.

## Lean clause audit by ND (author)

I reread the repaired stage-2 artifact against the source, clause by clause. The
source is `/home/ubuntu/work-bp/sheaf/literature/stacks-project/varieties.tex:7010-7018`,
Section 33.36 (tag 0CC6), immediately before Definition 33.36.1. It has exactly two mathematical
clauses: `p` is a prime number, and a scheme `X` has characteristic `p` when `p` is zero in its
structure sheaf. The delivered declaration is in
`lean/Sheaf/Paper/SchemeCharacteristicP.lean`, under `namespace AlgebraicGeometry.Scheme`:

```lean
def IsOfCharacteristic (X : Scheme.{u}) (p : ℕ) (_hp : p.Prime) : Prop :=
  ∀ U : X.Opens, (p : Γ(X, U)) = 0
```

The node's complete `lean` record is:

```json
{
  "module": "Sheaf.Paper.SchemeCharacteristicP",
  "declaration": "AlgebraicGeometry.Scheme.IsOfCharacteristic",
  "file": "lean/Sheaf/Paper/SchemeCharacteristicP.lean",
  "statement": "def IsOfCharacteristic (X : Scheme.{u}) (p : ℕ) (_hp : p.Prime) : Prop",
  "branch": "newtargets-dag",
  "by": "ND",
  "date": "2026-10-16",
  "existing": false
}
```

The prime-number clause is represented by `_hp : p.Prime`; the underscore records that the
proof is not needed by the defining predicate. The scheme clause is represented by
`X : Scheme.{u}`. “Zero in its structure sheaf” is represented exactly by quantifying over
every open `U : X.Opens` and requiring the natural-number cast `p : Γ(X, U)` to equal zero.
No global-sections, stalk, or factorization equivalence has been added. For the empty scheme,
the condition is the zero-section condition in the zero ring.

The module and declaration docstrings identify Stacks tag 0CC6 and the blueprint id. The
required per-file compile was:

```text
python3 /home/ubuntu/weil-launcher-nt/scompile.py ND def-weil-scheme-characteristic-p /home/ubuntu/weil-newtargets-sandbox/ND/def-weil-scheme-characteristic-p/lean/Sheaf/Paper/SchemeCharacteristicP.lean
sandbox Sheaf/Stage2/Sandbox0.lean
(with the modules compiled into /tmp/nt-local-compile-dh50n_n7/.lbuild) [3.2 s]
library Sheaf/Paper/SchemeCharacteristicP.lean
[3.1 s]
```

The command exited 0 with no warnings. `tools/stage2_delivery.py decls` independently returned
`AlgebraicGeometry.Scheme.IsOfCharacteristic` with the verbatim signature recorded above. I
also read Mathlib's `Scheme` and `Γ` definitions and the source's global-section hypothesis in
`WeilConjectures/AlgebraicGeometry/AbsoluteFrobenius.lean`; that hypothesis is the `U = ⊤`
consequence, not a replacement for this definition.

The existing stage-1 dependency `def-pc-scheme` supplies the scheme and structure-sheaf section
objects. The broader explanatory node `def-weil-locally-ringed-space-morphism` is not used as a
separate Lean term by this definition, and no private replacement was introduced. No new
definition node or dependency module was needed for this repair.

## New nodes

None.

## Dependency modules

None. The item module uses Mathlib's `AlgebraicGeometry.Scheme` directly; the stage-1 dependency
records remain unchanged.

## H1 repair: stage-2 definition, verbatim record, and compile evidence

The immutable-head return identified missing stage-2 artifacts. This repair supplies the actual
module, the complete `lean` record, an author clause-by-clause Lean audit for the fresh second reader, and the clean
`scompile.py` evidence above. H11 still requires the fresh second reader named in this assignment;
this author audit does not claim to be an independent reading. No live repository or compiled library was modified.

## Statement corrected

The stage-2 dry run exposed that the prior source-faithful prose simplification had not been
recorded relative to the published base. Added the required `statement_change` record with the
base wording and dependencies verbatim. This removes redundant characterizations from the
definition, while retaining precisely the same predicate and prime domain. Both base citers
`def-weil-absolute-frobenius-scheme` and `lem-weil-absolute-frobenius-well-defined` use only
vanishing on the structure sheaf, so both uses still hold. No target statement is changed.

Stage-1 validation: `deliver.py ND def-weil-scheme-characteristic-p --no-push` printed
`OK (not pushed) deliver/ND/def-weil-scheme-characteristic-p at 0a26ff8b5e: preflight passed`.
This checks the DAG packet; the stage-2 dry run is separately required for the Lean artifact.

## Second reading by ND

I independently reread the item against Stacks, Varieties, Section 33.36 “Frobenii”,
section label `section-frobenius`, tag 0CC6, first paragraph before Definition 33.36.1
(label `definition-absolute-frobenius`, tag 03SM). The source says exactly that a prime
number p is zero in the structure sheaf of X. The item's clause “for every open U, the
section p·1 in O_X(U) is zero” is the direct sectionwise meaning of that sentence; its
prime hypothesis and the empty-scheme convention agree with the source and its vacuous
case.

There are no proof steps: this node is a definition, so no cited step or proof dependency
needed checking. The two statement dependencies were opened. `def-pc-scheme` supplies the
scheme X, and `def-weil-locally-ringed-space-morphism` defines the structure sheaf and its
section rings; both say exactly what the statement uses. No new nodes are present, so the
B1–B7 and duplicate-node checks are vacuous. A complete DAG and blueprint search found no
existing scheme-characteristic predicate or duplicate source clause. The recorded
LeanFinder, Loogle, grep, and unavailable LeanSearch searches in `searches.jsonl` found only
ring-level characteristic declarations, never a scheme-level predicate.

I tested the statement on the empty scheme (the sole section ring is the zero ring and the
condition is vacuous), on `Spec A` for a field A of characteristic p (the condition holds
on every section), on `Spec ℤ` (it fails for every prime p), and on the zero ring (the
sectionwise equation holds). These cases do not expose a missing hypothesis or a weakened
conclusion.

Changed: added the exact Stacks section and definition labels to the node's source place,
so the citation identifies the tag and labels required by B5. I also removed the stale
stage-2 wording from `split_report.summary`; this delivery is stage 1 only. Removed the
sandbox-only `lean` and `statement_change` fields: preflight check 9 rejected the latter
as a maintainer field, and the former described a module outside this stage-1 packet.
The first worker’s stage-2 sections above are retained as history; they are not claims
about this delivery. No Lean file was changed or compiled in this second reading.
No mathematical clause, dependency, or proof field was changed.

Independent searches: LeanFinder query “scheme has characteristic p if p is zero in
structure sheaf” returned ring characteristic declarations only. A fresh grep for
`CharP|IsOfCharacteristic|ringChar` in Mathlib/AlgebraicGeometry returned 15 uses on
elliptic-curve coefficient rings. Loogle query `"CharP"` returned ring-level
`Lean.Grind.IsCharP` declarations. The earlier natural-language Loogle attempt was a
parse error, and the earlier grep with `--subdirectory` searched an invalid path;
neither is used as absence evidence. All raw results remain in `searches.jsonl`.
`blueprint_refs.py search characteristic` checked 54 blueprint matches across all
chapters; none defines this scheme predicate. The ancestor command confirmed
`def-weil-frobenius-detailed`.
