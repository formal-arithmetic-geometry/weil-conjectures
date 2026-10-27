## Worker report

The module `Sheaf.AlgebraicGeometry.DvrFlatGenericSubgroupClosure` states
`AlgebraicGeometry.exists_dvr_flat_generic_subgroup_closure`. Its sole theorem
has proof `sorry`; there are no new definitions, helper theorems, or axioms.
The node is unchanged except for its `lean` field.

I read Conrad, *Reductive group schemes*, Theorem 5.3.5 proof, printed p.166
(PDF page index 165), at
https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf. The paragraph identifies
the schematic closure as a separated flat subgroup and factors the original
flat source through it. The node expands this argument to arbitrary flat sources
and spells out the local kernel construction, without assuming the ambient group
flat. The accepted eight-step proof is reproduced in the theorem docstring.

Hypothesis and clause correspondence:

| Node | Lean rendering |
| --- | --- |
| DVR R | `R : Type u`, `[CommRing R] [IsDomain R] [IsDiscreteValuationRing R]`; the last class extends local principal ideal ring and excludes fields. |
| Fraction field K | `K : Type u`, `[Field K] [Algebra R K] [IsFractionRing R K]`. |
| S = Spec R | All base objects lie in `Over (Spec (.of R))`. |
| S-group G with group diagrams | `G : Grp (Over (Spec (.of R)))`; bundled group objects contain multiplication, identity, inverse and their diagrams. |
| G separated | `[IsSeparated G.X.hom]`. |
| G finite type | `[LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]`, exactly the recorded convention. |
| No flatness hypothesis on G | There is no `Flat G.X.hom` binder. |
| Generic fibre | Pullback along `Spec.map (CommRingCat.ofHom (algebraMap R K))`, with its canonical group structure via `(Over.pullback ...).mapGrp`. |
| Closed subgroup H_K of G_K | `H : Grp (Over (Spec (.of K)))`, a group homomorphism `j : H ⟶ ...obj G`, and `[IsClosedImmersion j.hom.hom.left]`. A closed immersion is monic, so this is precisely a closed subgroup, with no extra smoothness, reducedness, or affineness. |
| C a closed subscheme of G | Existential `C : Grp (Over (Spec (.of R)))`, `i : C ⟶ G`, and `IsClosedImmersion i.hom.hom.left`. |
| Its ideal on each affine V = Spec B is the stated kernel | For every `V : G.X.left.affineOpens`, `i.hom.hom.left.ker.ideal V` equals `RingHom.ker` of `(j.hom.hom.left ≫ pullback.fst ...).app V`. Here `f.app V` is the restriction homomorphism from sections on V to sections on its inverse image in H; that inverse image is canonically `V ×_G H`. Thus this is the exact kernel in the node, including scheme structure. |
| These ideals define C | Existence of the same closed immersion with the displayed ideal equality on every affine open asserts the gluing and specifies its closed subscheme uniquely. The chosen presentation is existential, rather than a choice of an unspecified object used in a definition. |
| C_K = H_K as closed subschemes of G_K | `∃ e : (Over.pullback ...).obj C.X ≅ H.X`, with `e.hom ≫ j.hom.hom = (Over.pullback ...).map i.hom.hom`. This is an isomorphism over Spec K commuting with the embeddings into G_K, not just an abstract isomorphism. |
| Restricted operations | The existential C is a group object and i is a morphism in `Grp`; its unit and multiplication commute with those of G, and therefore so does its inverse. As the inclusion is monic these are exactly the restrictions. |
| C separated and flat | `IsSeparated C.X.hom ∧ Flat C.X.hom`. |
| C finite presentation | `LocallyOfFinitePresentation C.X.hom ∧ QuasiCompact C.X.hom ∧ QuasiSeparated C.X.hom`, the node's Stacks 01TP convention. |
| Every flat S-scheme X | `∀ (X : Over (Spec (.of R))) ... Flat X.hom → ...`; X has no group structure and no finiteness or separatedness condition. |
| Every S-morphism v whose generic map factors through H_K | `v : X ⟶ G.X` and an existential ordinary slice morphism `w` from X_K to H.X satisfying the generic factorization equation. |
| Unique factorization through C | `∃! w : X ⟶ C.X, w ≫ i.hom.hom = v`; uniqueness is among all S-morphisms, not merely homomorphisms. |

All universes and variables are explicitly bound. Schemes and test schemes use
the same ambient universe u; the fraction-field extension is not an independent
universe that could make the test condition empty. The theorem permits all
characteristics, nonreduced subgroups, and nonaffine groups.

Dependency declarations read and reused:

- `def-sc-discrete-valuation-ring`: `IsDiscreteValuationRing`,
  `Mathlib.RingTheory.DiscreteValuationRing.Basic` (mathlib_match, no lean record needed).
- `def-weil-affine-spectrum`, `def-pc-scheme`: `AlgebraicGeometry.Spec`, `Spec.map`,
  `Scheme`, `Scheme.Hom`, `Mathlib.AlgebraicGeometry.Scheme`.
- `def-weil-proper-morphism`: `AlgebraicGeometry.IsSeparated`, reexported by its
  recorded `Mathlib.AlgebraicGeometry.Morphisms.Proper` module. Properness is not assumed.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`,
  `QuasiCompact`, through `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`.
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion`,
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`.
- `def-pc-base-change`: import the recorded
  `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`; as its record explicitly
  instructs, scheme and morphism base change are `CategoryTheory.Over.pullback`,
  with underlying `Limits.pullback`, `pullback.fst` and `pullback.snd`.
  The recorded module's module-sheaf pullback is irrelevant here.
- `def-weil-flat-morphism`: `AlgebraicGeometry.Flat`,
  `Mathlib.AlgebraicGeometry.Morphisms.Flat`.
- `def-weil-pbc-scheme-conventions`: a convention-only node, with no module or
  declaration by design. Finite presentation uses `LocallyOfFinitePresentation`,
  `QuasiCompact`, `QuasiSeparated`, as its record instructs.
- Existing `Grp`, `GrpObj`, group-object morphisms, and functorial `mapGrp` are the
  Mathlib group-object interface; `Mathlib.CategoryTheory.Monoidal.Cartesian.Over`
  supplies the canonical pullback group construction.
- The ideal formula reuses `Scheme.Hom.ker` and `IdealSheafData.ideal` from
  `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`, the recorded ideal-sheaf dependency.
  No second notion of schematic closure is introduced.

Proof-only dependencies are available through ordinary imports of
`Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`,
`Mathlib.RingTheory.Flat.TorsionFree`, `Mathlib.RingTheory.FinitePresentation`,
and `WeilConjectures.RingTheory.FlatModuleAtPrime`. They provide the affine
closed-subscheme construction, torsion-free/flat equivalence and implication,
Noetherian finite-presentation result, and localized-module flatness criterion.
Other recorded proof leaves (affine fibre products, separated implies
quasi-separated, flat affine criterion, flat ring maps, Noetherian rings) are
already in the imported dependency closures.

Edge cases checked mathematically before writing:

- For the additive group `Spec R[x]/(πx)`, the ambient group is not flat and its
  generic fibre is the identity subgroup. Its closure has ideal (x), giving Spec R;
  the signature retains this case because G has no flatness assumption.
- In characteristic p, the subgroup α_p has closure `Spec R[x]/(x^p)`; neither
  reducedness nor smoothness is required.
- If G is flat and H_K = G_K, the kernel is zero and C = G. If G has vertical
  torsion, the kernel removes that torsion rather than presupposing it zero.
- The trivial subgroup is allowed. The generic subgroup cannot be empty because
  its group identity is a section over the nonempty Spec K. Empty affine charts
  and an empty test source X cause no restriction; the latter has a unique map.
- Flat sources need not be quasi-compact or separated. Both the factorization
  hypothesis and uniqueness use ordinary slice maps, so all such sources are covered.
- Nonflat sources can carry vertical maps invisible generically; the explicit
  flatness premise is essential and has not been dropped.

Searches performed with msearch.py (group Q33, this item):

- LeanFinder: `schematic closure of a generic closed subgroup over a discrete
  valuation ring is flat and is a group scheme`. Eight hits, including
  `ValuativeCommSq.valuationRing`, `Flat`, `Flat.generalizingMap`, residue closed
  immersions and valuative-square field/algebra instances. No closure theorem.
- Loogle: `AlgebraicGeometry.Scheme.Hom, AlgebraicGeometry.Flat`. Zero hits.
- Mathlib grep in AlgebraicGeometry:
  `schematicClosure|schematic.closure|schemeTheoreticImage`. Zero hits by those names.
- LeanSearch: `The schematic closure of a closed subgroup of the generic fibre
  over a DVR is a flat closed subgroup`. Eight hits, all topological closed subgroup
  definitions and topological closure results, not scheme-theoretic closure.
- Direct rg with the same closure pattern in `lean/WeilConjectures` and `lean/Sheaf`:
  existing special-case closure interfaces and reduced scheme-image results, none
  stating this generic-subgroup theorem. In particular
  `Sheaf.TraceFormula.ValuationHorizontalCurveModels.FlatClosure` has additional
  curve/pure-dimension-zero conditions and is not this theorem.
- Direct rg for this node id in `lean/WeilConjectures`: no occurrence.
- Inspected Mathlib `IdealSheaf.Basic` and `IdealSheaf.Subscheme` directly after
  finding existing uses of `f.ker` and `f.image`: these give the existing ideal
  and closed-subscheme APIs, not the subgroup theorem. Read `Hom.ker` and
  `Hom.ker_apply`; the latter's quasi-compactness condition does not become a
  hypothesis here, since the exact local kernel equality is part of the conclusion.
- Inspected upstream `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs` and the
  Mathlib group and slice APIs. The former's closed-subgroup class specializes to
  fields; Mathlib's general group objects over a scheme give precisely the needed
  group diagrams without a duplicate definition or a dependency repair.

Validation: scompile.py compiled the single delivered module both as a sandbox
module and at its intended library module path (15.1 s and 2.5 s respectively),
with no errors or unexpected warnings. No local or global build was run.
No statement correction or STATEMENT-DISPUTED issue was needed.

## Second reading by Q33

No second worker was started, as the dispatch brief forbids delegation. The
maintainer's independent review reads the delivery. A final self-check compared
the displayed signature with the unchanged node, in particular the absence of
flatness on G, equality of embedded generic fibres, the affine kernel formula,
all three finite-presentation conditions, and uniqueness for arbitrary flat sources.
