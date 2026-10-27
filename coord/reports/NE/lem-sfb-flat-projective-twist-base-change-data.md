## Worker report

The module `Sheaf.AlgebraicGeometry.FlatProjectiveTwistBaseChangeData` states
`AlgebraicGeometry.FlatProjectiveTwist.flat_projective_twist_base_change_data`.
Its only postponed proof is that theorem, with the six-step DAG proof in its docstring.
All helper definitions have actual data. No node statement is corrected, no new nodes
are introduced, and no dependency records are replaced.

Hypothesis-by-hypothesis and clause-by-clause reading:

- `T Z : Scheme.{u}`, `n : ℕ`, and
  `i : Z ⟶ RelativeProjectiveSpace.scheme T n` are the arbitrary base, embedded
  scheme, nonnegative projective dimension, and stated relative-Proj projective space.
  `[IsClosedImmersion i]` is precisely the closed-embedding hypothesis.
- Every occurrence of the structural map is `i ≫ RelativeProjectiveSpace.π T n`.
  `[Flat ...]`, `[LocallyOfFinitePresentation ...]`, `[QuasiCompact ...]`, and
  `[QuasiSeparated ...]` are exactly the flatness and finite-presentation hypotheses.
  In particular, an unrelated flat map `Z ⟶ T` is never substituted.
- `comparison T n` selects the UNIQUE comparison from the recorded
  `existsUnique_freeProjectiveBundleBaseChangeSpace`. Its characterization fixes the
  structure map and every affine polynomial/Proj comparison, including restriction.
  No object is chosen from uncharacterized existence. `relativeTwist T n d` is the
  actual tensor pullback of the recorded `ProjectiveSpace.twist` along this comparison;
  `twist i d` is its actual tensor pullback along i. Thus it is the canonical glued
  restriction of the affine twists in the statement. The global integral-model
  construction is already available, so a second sheaf-gluing construction is unnecessary.
- `chart i j` is the inverse image of the standard coordinate chart, via that fixed
  comparison. `frame i d j` is the actual section `1 ⊗ (1 ⊗ x_j^d)` obtained by the
  recorded section-normalized tensor pullback and the upstream integral-model twist.
  `Proj.twistPowSection` uses the actual fraction `1 / x_j^(-d)` in negative degree.
  These bases are the affine restrictions specified by the node, and determine all
  claimed identifications on every affine base restriction.
- The first conclusion `IsProper (i ≫ ...π...)` is properness of exactly f.
- The second conclusion quantifies `d : ℤ` and asserts `(twist i d).IsInvertible`
  and `.IsFinitePresentation`, the recorded sheaf notions, with no base Noetherianity.
- For every `z : Z`, the displayed `Module.Flat` uses the base stalk
  `T.presheaf.stalk (f z)`. Its module is the recorded
  `RingedSpace.moduleStalkFunctor Z.toRingedSpace z` applied to `twist i d`, restricted
  along the actual ring map `(f.stalkMap z).hom` by `ModuleCat.restrictScalars`.
  This is precisely the requested stalkwise base flatness, not merely flatness over Z.
- `D : PowerData i` gives an actual internal-Hom dual identification in degree -1,
  normalized by `dualEvaluation` to send the basis pair to 1, and all the signed-power
  isomorphisms. `signedPower M (.ofNat m)` is `M.tensorPow m`, including the structure
  sheaf at m=0. `signedPower M (.negSucc m)` is `(dual M).tensorPow (m+1)`. `normalized`
  sends each twist basis to the pure tensor basis `powerFrame`, so arbitrary scalar
  multiples of those isomorphisms cannot satisfy the condition.
- For every scheme `T' : Scheme.{u}` and every `h : T' ⟶ T`, `i'` has source the
  chosen fibre product `pullback f h`, with structure map `pullback.snd f h`.
  The structural equation and `IsPullback (pullback.fst f h) i' i (projectiveMap n h)`
  identify it as the induced embedding into the SAME relative-Proj space over T'.
  `projectiveMap` is the conjugate of the actual projective-space base-change map;
  thus its data is canonical. `IsClosedImmersion i'` is explicitly concluded.
- `β d` is the isomorphism `h_Z^* F_d ≅ i'^* O(d)` for every integer degree.
  `IsFrameComparison` fixes it on the pulled coordinate basis on every common subopen.
  Common subopens avoid hidden casts between preimage opens; the cartesian embedding
  ensures that the corresponding coordinate charts agree.
- `D' : PowerData i'` specifies the SAME tensor and dual conventions after base change.
  `κ d` is the comparison on the signed tensor powers, also fixed on the pure tensor
  bases by `IsFrameComparison`. Its negative-degree rule uses the evaluation-normalized
  dual bases. Finally the displayed morphism equality says
  `h_Z^*(D.iso d) ≫ κ d = β d ≫ D'.iso d` for all integers d. This is the requested
  tensor-power compatibility, including the unit and dual cases. The basis normalization
  fixes the canonical tensor/dual transport rather than allowing arbitrary maps.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Scheme.Hom.stalkMap`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion` and its
  base-change stability instance (the proof dependency is a Mathlib match).
- `Sheaf.AlgebraicGeometry.RelativeProjectiveSpace`: `RelativeProjectiveSpace.scheme`,
  `π`, `construction`, and the affine polynomial/coordinate interface, obtained by the
  public import of the comparison module.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`, equivalently `Flat.iff_flat_stalkMap`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: `LocallyOfFinitePresentation`;
  `Morphisms.QuasiSeparated` supplies `QuasiSeparated` and the imported quasi-compact API.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist`: `ProjectiveSpace.twist`,
  pulled back from `Proj.twist`, and `ProjectiveSpace.toProjInt` from `ProjectiveSpace`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: `Scheme.Modules.tensorPullback`
  and `tensorPullbackSection`. This is the recorded normalized dependency, not a private
  pullback definition or an arbitrary choice of an adjunction.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`: `IsInvertible` and `tensorPow`;
  `Modules.Dual`: `dual`, definitionally the internal Hom into the structure module,
  and `dualEvaluation`; `Modules.TensorSection`: `tmulSection`, `unitSectionsEquiv`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`: `SheafOfModules.IsFinitePresentation`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, `fst`, `snd`,
  obtained through the projective-space public imports; its universal property is `IsPullback`.
- `Mathlib.RingTheory.RingHom.Flat` / `Mathlib.RingTheory.Flat.Basic`: `Module.Flat`,
  obtained through `Morphisms.Flat`. No private flatness predicate is introduced.
- The proof imports additionally include the recorded `Morphisms.Projective`,
  `Topology.GlueSheavesOfModules`, `RelativeProj.BaseChange`, and
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` modules. The projective-space
  properness result is already publicly supplied by `ProjectiveSpace.Twist`.
- `Sheaf.AlgebraicGeometry.FreeProjectiveBundleBaseChangeSpace`:
  `existsUnique_freeProjectiveBundleBaseChangeSpace`, read in full, supplies the uniquely
  affine-normalized over-isomorphism used by `comparison`. It is already a proof dependency.
- `WeilConjectures.Algebra.Homology.ModuleStalkFunctor`: `RingedSpace.moduleStalkFunctor`;
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts` supplies the standard-open API.

Source checks: read Stacks `constructions.tex`, labels `lemma-when-invertible` and
`lemma-apply-modules` (01MS/01MT), and `morphisms.tex`, label
`lemma-locally-projective-proper` (01WC). Their bases, multiplication maps and arbitrary-base
properness agree with the node's six proof steps. The relative-Proj and comparison source
modules were read, including their affine restriction formulas. No current blueprint text
for this extracted node was found by searching its id in `literature/blueprint/latest`.

Edge cases checked before drafting: n=0 has exactly one coordinate; the coordinate type is
`ULift (Fin (n+1))` in the scheme universe. d=0 uses the structure module and basis 1; d=-1
uses the actual dual and evaluation; other negative d use positive powers of that dual.
Empty Z or T are permitted (no Nonempty hypothesis); the pointwise conditions become empty
only where the mathematics itself is empty. No Noetherian, affine-intersection, reducedness,
characteristic, or flatness condition on h is introduced. Arbitrary base morphisms and the
identity morphism use the same comparison. All schemes share the usual scheme universe u;
there is no independent smaller test-object universe. The theorem has no `let`, implicit
unbound variable, file-local notation or private declaration.

Searches for the statement and its constructions (2026-10-24):

- `msearch.py leanfinder`, query "Flat projective scheme twists invertible modules finite
  presentation and canonical arbitrary base change": eight hits on module flatness,
  projectivity and the scheme-flat predicate, no statement matching this node.
- `msearch.py loogle`, query "AlgebraicGeometry.ProjectiveSpace.twist,
  AlgebraicGeometry.Scheme.Modules.tensorPullback": zero hits; the remote index does not
  recognize the project-specific first identifier.
- `msearch.py grep`, query `twist.*[Bb]ase[Cc]hange|[Bb]ase[Cc]hange.*twist|tensorPow`,
  subdirectory AlgebraicGeometry: zero Mathlib hits.
- `msearch.py leansearch`, query "An invertible twisting sheaf on a flat projective scheme
  is finitely presented and flat over the base and commutes with arbitrary base change":
  eight hits, including `SheafOfModules.isFinitePresentation` and algebra/module
  base-change finite-presentation lemmas; no matching projective-family statement.
- `rg` in `lean/WeilConjectures/AlgebraicGeometry` and `lean/Sheaf/AlgebraicGeometry`, query
  `flatProjective|flat_projective|twist.*baseChange|twist.*BaseChange|relative.*[Tt]wist`:
  found the already recorded twist and tensor APIs, the relative-Proj comparison and
  `FlatProjectiveHilbertPolynomialLocality`; the latter asserts Hilbert polynomials and
  does not assert this node's twist data. No exact statement exists.
- `grep -rn` of this node id in `lean/WeilConjectures`: no match.
- `rg` for `framePower`, `powerFrame`, `PowerData` and `IsFrameComparison` found no existing
  version of these node-specific normalized data. The abstract
  `NormalizedSignedPowers.signedPower` uses duals of entire positive powers and requires
  separate monoidal data; here `signedPower` merely abbreviates the exact powers of the
  degree-one dual specified by this node, using the existing `tensorPow` and `dual`.

Validation: `scompile.py NE lem-sfb-flat-projective-twist-base-change-data` compiled the
module separately in sandbox and its library namespace against the published server build,
with exit 0 and no errors or non-sorry warnings. The initial diagnostic missing the
standard-open public import and the local polynomial grading instance was repaired by
using `ProjectiveSpace.Charts` and a concrete `letI` inside the frame definition (data,
not a statement binder). Only the final theorem contains `sorry`.

No STATEMENT-DISPUTED issue or node fault was found.

## Second reading by NE

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
