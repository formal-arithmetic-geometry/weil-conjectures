## Worker report

The delivery states `AlgebraicGeometry.neronLft_neutralAffineProductChart` in `Sheaf.AlgebraicGeometry.NeronLftNeutralAffineProductChart`, with its proof `sorry`. The only other declaration, `AlgebraicGeometry.groupOpenProductMap`, constructs the canonical multiplication restricted to an open subscheme using the tensor of its two inclusions followed by the group's multiplication. Its data contain no postponed proof, choice of an arbitrary arrow, or additional assumption. This is a helper for the product map already in the item's statement, not an independent new notion.

The original statement, dependencies, proof and all other node fields are unchanged; only `lean` is added. No dependency repair or new definition node is needed. `GrpObj` is defined in any cartesian monoidal category, so its existing dependency record also supplies the relative group objects over `Spec D`, despite the informal definition node being phrased over fields.

Hypotheses and conclusions correspond as follows:

| Node clause | Lean rendering |
| --- | --- |
| Noetherian integrally closed domain D of dimension one | `(D : Type u) [CommRing D] [IsDomain D] [IsNoetherianRing D] [IsIntegrallyClosed D]` and `_hDim : ringKrullDim D = 1` |
| K is the fraction field of D; S is Spec D | `(K : Type u) [Field K] [Algebra D K] [IsFractionRing D K]`; every base occurrence is `Spec (.of D)` and the generic inclusion is `Spec.map (CommRingCat.ofHom (algebraMap D K))` |
| V/K is a commutative group scheme | `V : Grp (Over (Spec (.of K)))` with `[IsCommMonObj V.X]`; bundled `Grp` contains `GrpObj`, including multiplication, inverse, identity and their diagrams |
| V is smooth, separated and of finite type | `[Smooth V.X.hom] [IsSeparated V.X.hom] [LocallyOfFiniteType V.X.hom] [QuasiCompact V.X.hom]`; finite type is the conjunction of the latter two existing notions |
| N/S is smooth, separated and commutative | `N : Grp (Over (Spec (.of D)))` with `[IsCommMonObj N.X] [Smooth N.X.hom] [IsSeparated N.X.hom]`; separatedness means the diagonal is a closed immersion, as in Mathlib's `IsSeparated` |
| Specified generic-fibre group isomorphism | `α : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D K)))).mapGrp.obj N ≅ V`; the isomorphism is in the category of group objects, hence respects the group structures |
| Restriction gives a bijection for every smooth S-scheme Y | `_hNeron : ∀ (Y : Over (Spec (.of D))) [Smooth Y.hom], Function.Bijective (fun h : Y ⟶ N.X ↦ (Over.pullback ...).map h ≫ α.hom.hom.hom)`; these are **all scheme morphisms over the base**, not just group homomorphisms, and Y is not assumed finite type or quasi-compact |
| C is the union of geometric fibre identity components | The equality for `(C : Set N.X.left)` uses `x ∈ connectedComponentIn (N.X.hom ⁻¹' {N.X.hom x}) (η[N.X].left (N.X.hom x))`, the ordinary fibre component through the identity. `section_component_preimage_of_isPullback` identifies this locus after every field base change with the corresponding geometric fibre component; this is precisely step 1 of the node's proof, not a different notion or an extra hypothesis |
| C is open | `C : N.X.left.Opens` with the preceding exact equality |
| Its open subscheme structure is a subgroup N^0 of N | `∃ (H : Grp (Over (Spec (.of D)))) (j : H ⟶ N), IsOpenImmersion j.hom.hom.left ∧ Set.range j.hom.hom.left = (C : Set N.X.left)`. The morphism in `Grp` is a group homomorphism. An open immersion with image C identifies H canonically, over N, with C's open subscheme, including its structure sheaf; no weaker abstract subgroup or merely bijective map is used |
| For every s there is an affine open base neighbourhood B | `∀ s : Spec (.of D), ∃ B : (Spec (.of D)).Opens, s ∈ B ∧ IsAffine B.toScheme ∧ ...` |
| U is an affine open subscheme of N^0 ×_S B | `∃ U : ((Over.pullback B.ι).mapGrp.obj H).X.left.Opens, IsAffine U.toScheme ∧ ...`; the underlying object of `Over.pullback` is the recorded scheme fibre product |
| Its multiplication U ×_B U → N^0 ×_S B is surjective on underlying points | `Surjective (groupOpenProductMap ((Over.pullback B.ι).mapGrp.obj H) U)`. The helper's source is the tensor of `Over.mk (U.ι ≫ G.X.hom)` with itself in `Over B`, hence exactly U ×_B U. The map is the tensor of the inclusions followed by `μ[G.X]`, not a freely chosen map |
| Image is the whole open subgroup, without finite component groups | The target is exactly the base-changed H; `Surjective` gives the full image. There is no finiteness, connectedness, or quasi-compactness hypothesis on N, its total space, or its component groups |

All variables and the universe `u` are explicit and `autoImplicit` is false. The ring, schemes, test schemes and field extensions can be placed in any common universe; no separate smaller test-object universe makes the mapping property vacuous. Bundling the open subgroup via its open immersion is equivalent to taking the actual open subscheme C, since open immersions identify structure sheaves as well as spaces.

Dependency declarations read and used:

- `def-weil-affine-spectrum`, `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Spec`, `Spec.map`, `Scheme`, `Scheme.Hom`.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `AlgebraicGeometry.Smooth`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `AlgebraicGeometry.LocallyOfFiniteType`; `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, `AlgebraicGeometry.QuasiCompact`.
- `def-pc-base-change`: `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`, documenting `Over.pullback` and its canonical scheme fibre products and projections. This is the recorded upstream module, not the withdrawn Sheaf twin.
- `def-sc-group-scheme`: `Mathlib.CategoryTheory.Monoidal.Grp`, `CategoryTheory.GrpObj` and `Grp`; `Mathlib.CategoryTheory.Monoidal.Mon`, `IsCommMonObj`, `IsMonHom`. The relative pullback group structure is the existing `Over.pullback.mapGrp`, supplied by `Mathlib.CategoryTheory.Monoidal.Cartesian.Over` through `Mathlib.AlgebraicGeometry.Group.Affine`.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, `AlgebraicGeometry.IsClosedImmersion`, used through `Mathlib.AlgebraicGeometry.Morphisms.Separated`, `IsSeparated` (its defining field is `IsClosedImmersion (pullback.diagonal f)`).
- `def-weil-connected-scheme`: Mathlib match `ConnectedSpace`, `Mathlib.Topology.Connected.Basic`; its actual `connectedComponentIn` is used directly, without a private component predicate.
- `def-weil-geometric-fibre`, `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`, used through `Over.pullback` and the cartesian monoidal structure on the over category.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`, `AlgebraicGeometry.IsOpenImmersion`; the open subgroup conclusion uses exactly this notion.

The stated proof dependencies are imported privately, including `WeilConjectures.AlgebraicGeometry.SectionComponentPullback` (`section_component_preimage_of_isPullback`), `WeilConjectures.AlgebraicGeometry.SmoothSectionComponentOpen` (`Smooth.isOpen_section_component`), `Sheaf.AlgebraicGeometry.LocallyAlgebraicGroupIdentityComponent` (`locallyAlgebraicGroup_identityComponent`), and `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber` (`smooth_iff_flat_locallyOfFinitePresentation_smooth_fiberToSpecResidueField`). The remaining Mathlib proof-dependency modules cover affine quasi-compactness, continuous images, affine pullbacks, open factorization, flat-lfp openness, smooth ring base change/composition, the affine smoothness bridge, and surjective base change. The theorem docstring contains all five steps of the supplied proof, with their main DAG dependencies.

Source checked: the primary-source [BLR scan](https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf), PDF page 296, printed page 290, 10.1 paragraph following Definition 1; and PDF page 119, printed page 113, 5.1 Lemma 4. The former gives the local affine chart and product surjectivity of the neutral component of an lft-model; the latter gives the group multiplication restriction. No source correction is needed.

Edge cases checked before writing:

- The trivial group has H = N = S and admits the whole base chart; the component is nonempty in each fibre because of the identity section.
- The empty scheme cannot be a group scheme over the nonempty spectrum of a domain. Empty opens U are allowed by the type, but cannot witness surjectivity over a neighbourhood containing s; no nonempty hypothesis is artificially added.
- A nonzero split torus may have an lft-model with infinitely many components. N is not required quasi-compact or finite type; neither is its component group required finite.
- Zero-dimensional or disconnected generic groups are allowed. No positive relative dimension or geometric connectedness assumption is imposed on V.
- Arbitrary residue characteristics and imperfect residue fields are allowed; the section-component/geometric-component comparison is the existing base-change theorem, not a claim about rational points alone.
- The mapping property quantifies over every smooth test scheme in the common scheme universe, with no affine, finite-type or group restriction.

Searches performed (all actual queries):

- `msearch.py ... leanfinder "A smooth group scheme has an open neutral component locally covered by multiplication of an affine open with itself"`: 8 hits on ordinary affine covers and smooth loci, no matching neutral product chart.
- `msearch.py ... loogle "GrpObj, IsCommMonObj"`: no hits, with the service reporting `loogle: unknown identifier 'GrpObj'`; this is a failed name lookup, not evidence that the notions do not exist. Their actual Mathlib declarations were subsequently read and reused.
- `msearch.py ... grep "Neron|neutralComponent|sectionComponent|identityComponent" AlgebraicGeometry`: no hits in Mathlib.
- `msearch.py ... leansearch "A Neron lft model has an open identity component with local affine product charts"`: 8 hits on ordinary affine covers, Noetherian schemes, manifolds and localization of morphism properties, no matching theorem.
- `rg -l -i 'neron|néron|sectionComponent|section_component|neutral.*component|component.*neutral' lean/Sheaf lean/WeilConjectures`: found the existing section-component statements, locally algebraic identity-component theorem and field-group component definitions, but no Néron chart theorem. Those component interfaces were read; the existing statements are used in the proof imports, rather than redefined.
- `grep -rn 'lem-sfb-neron-lft-neutral-affine-product-chart' lean/WeilConjectures`: no match.
- `rg -n 'neron_lft_neutral_affine_product_chart|neronLft_neutralAffineProductChart' lean/Sheaf lean/WeilConjectures`: no match.
- `rg -n 'NeronLft|neronLft|groupOpenProductMap' lean/Sheaf lean/WeilConjectures lean/.lake/packages/mathlib/Mathlib`: no name collision.
- `rg -n 'restriction.*multiplication|restrict.*multiplication|ProductMap|open.*product.*[Mm]ap|[Oo]pen.*[Mm]ul'` in Mathlib and project algebraic geometry: no existing scheme open-product restriction construction. The short helper composes existing canonical inclusions and multiplication.
- DAG keyword searches found the already split neighbouring Néron nodes and the component-comparison lemmas; no separate definition is introduced.

Validation: the module compiled through the prescribed `scompile.py` in both sandbox mode and its final module name, in approximately three seconds each, with no error or non-sorry warning. The first check caught the extra projection required for bundled `Grp` morphisms; the projections were corrected to `j.hom.hom.left` and `α.hom.hom.hom`. Final imports are checked again by the delivery dry run.

No `STATEMENT-DISPUTED` flag or node fault remains.

## Second reading by Q10

This dispatcher worker performed a fresh clause-by-clause self-audit with the original JSON and final module open; this is not represented as a second independent agent review. The maintainer's independent review is requested by the dispatch workflow.

The audit checked all D/K conditions, both commutative group structures, smoothness/separatedness of both groups, finite type only for V, and the full Néron bijection on scheme morphisms. The generic isomorphism is in `Grp`, so it cannot lose its group-compatibility condition. The subgroup inclusion is also in `Grp`, is an actual open immersion, and has image exactly C, so its entire open subscheme structure agrees with the node. The base neighbourhood quantifier includes every point, including the generic point. The chart is an affine open in the actual base change of that subgroup, and its map is canonical multiplication, with surjectivity expressed by the scheme-morphism class. The section-component formula agrees with the geometric locus by the recorded cartesian theorem, with no extra choice of fibre points. The helper has actual data and introduces no axiom or theorem. No mathematical hypothesis or conclusion was changed during this rereading. Only the bundled-morphism projections identified by compilation were repaired. The single theorem remains `sorry`, as required for stage 2.
