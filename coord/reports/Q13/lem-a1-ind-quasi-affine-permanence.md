## Worker report

The shared DAG already contains the reviewed NN stage-1 split of this item, so this delivery
states that unchanged item and does not resplit or add DAG nodes. The module
`Sheaf.AlgebraicGeometry.IndQuasiAffinePermanence` defines
`AlgebraicGeometry.indQuasiAffineProperty`, the exact local predicate (P): for every affine
open `U` of the target and every compact open `K` in the pullback over `U`,
`K.ι ≫ pullback.snd f U.ι` is `IsQuasiAffineHom`. The pullback is the canonical scheme
model of the inverse-image open in the node statement. It then states
`AlgebraicGeometry.indQuasiAffineProperty_permanence` with proof `sorry`.

The theorem signature renders the three clauses as follows. Clause (1) is
`∀ (T : Scheme.{u}) (g : T ⟶ Y), indQuasiAffineProperty f →
indQuasiAffineProperty (Limits.pullback.snd f g)`, so the base-change morphism is arbitrary.
Clause (2) is quantified over an arbitrary index type `I : Type v`, a family
`U : I → Y.Opens`, affine hypotheses `∀ i, IsAffineOpen (U i)`, and the cover equation
`iSup U = ⊤`; its conclusion is
`indQuasiAffineProperty f ↔ ∀ i,
indQuasiAffineProperty (Limits.pullback.snd f (U i).ι)`. Clause (3) is
`∀ (_hY : IsAffine Y), indQuasiAffineProperty f → ...`; it says every compact open
`K : X.Opens` (`IsCompact (K : Set X)`) has `K.toScheme.IsQuasiAffine`, and concludes
`Scheme.IsSeparated X ∧ QuasiSeparatedSpace X`. The explicit affine hypothesis is the
node's “if `Y` is affine”, and the final conjunction renders “separated, hence
quasi-separated”. The index universe is independent (`v`), so empty and infinite covers
remain included.

The statement dependencies used are the recorded declarations:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` from `Mathlib.AlgebraicGeometry.Scheme`.
- `def-nagata-quasi-affine-morphism`: `AlgebraicGeometry.IsQuasiAffineHom` from
  `WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine`.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback` and its projections from
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback` (provided by the public
  pullback imports).
- `def-weil-proper-morphism`: `AlgebraicGeometry.IsProper` and its separated component
  from `Mathlib.AlgebraicGeometry.Morphisms.Proper`.
- `def-weil-quasi-separated-morphism`: `AlgebraicGeometry.QuasiSeparated` from
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`.

The stated proof dependencies are imported where they have Lean modules: the ordinary
quasi-affine base-change theorem is `AlgebraicGeometry.isQuasiAffineHom_baseChange` in
`Sheaf.AlgebraicGeometry.QuasiAffineBaseChange`. The remaining proof dependencies are
Mathlib leaves or the unsplit child locality node; no unavailable declaration is copied.

I checked the edge cases represented by the signature: `I` may be empty (the cover equation
then forces the target to be empty), `I` may be infinite, `K` may be empty, and `X` or `Y`
may be empty. No finite-type, quasi-compactness, separatedness, or nonemptiness hypothesis
was added. The affine-base clause applies only under its explicit `IsAffine Y` hypothesis.

Searches made:

- `msearch.py ... leanfinder "ind quasi-affine morphism property stable under arbitrary base
  change affine open cover separated"`: generic `HasAffineProperty` locality hits and
  absolute quasi-affine declarations; no exact ind-quasi-affine permanence theorem.
- `msearch.py ... loogle "AlgebraicGeometry.IsQuasiAffineHom, Scheme.IsSeparated,
  QuasiSeparatedSpace"`: 0 hits; Loogle reports the project-specific identifier as unknown.
- `msearch.py ... grep "ind.?quasi.?affine|IndQuasiAffine" WeilConjectures`: 0 hits.
- `rg` over `WeilConjectures/` found no ind-quasi-affine declaration; `rg` over the existing
  Sheaf files found only the downstream fpqc-descent statement and its proof reference.
- `grep -rl 'ind-quasi-affine' dag/nodes` found the existing item and its downstream nodes;
  `python3 tools/blueprint_refs.py search quasi-affine` found only the already recorded
  ordinary quasi-affine nodes, and `ancestor` confirms `lem-a1-affine-hc0`.

No statement correction, dependency repair, new node, or `STATEMENT-DISPUTED` flag is needed.

## Second reading by Q13

I reread the current item JSON and the module after compilation. The helper definition has
exactly the node's affine-open/compact-open/quasi-affine condition, with the canonical
pullback presentation used by the downstream recorded `hV` interface. The theorem has one
base-change clause, one arbitrary affine-cover equivalence, and one affine-base conclusion;
all hypotheses and all three conclusions are present in the same order. The `sorry` is the
only postponed proof. The signature compiled cleanly with `scompile.py`, including the
stated ordinary quasi-affine base-change import.
