## Worker report

Statement-only delivery of `AlgebraicGeometry.smooth_marking_normalization_twist` in
`lean/Sheaf/AlgebraicGeometry/SmoothMarkingNormalizationTwist.lean`. The sole postponed
proof is that theorem, with `by sorry`. All auxiliary definitions contain real terms;
the structure packages the supplied canonical fibre adjunction and its identification.
The mathematical statement and Lean module are unchanged in this repair. The item
adds eleven definition-owner edges to `stmt_deps`: ten landed owners and the new
`existing: true` comparison-definition node described below. No statement correction
or disputed statement is needed.

### Hypotheses and conclusions, clause by clause

| Node clause | Lean rendering |
| --- | --- |
| Locally Noetherian base S | `[IsLocallyNoetherian S]` |
| Proper, flat, finitely presented f | `[IsProper f] [Flat f] [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]` |
| Every geometric fibre | `hfibres`, quantified over every `Ω : Type u`, `[Field Ω] [IsAlgClosed Ω]`, `t : Spec (.of Ω) ⟶ S`; fibre is `pullback f t`, structural map `pullback.snd f t` |
| Nonempty, reduced, pure dimension one, with no connectedness hypothesis | `IsSmoothMarkingGeometricFibre`: `Nonempty Y ∧ IsReduced Y ∧ Y.IsPureDimension 1`; no connected-space condition is imposed |
| Node condition only at nonsmooth closed points, over Ω | Same predicate: `IsClosed {y} → y ∉ p.smoothLocus → ∃ e : AdicCompletion ... ≃+* MvPowerSeries (Fin 2) Ω / (uv)`, with the explicit constant equation `e(completion.of(germ(p#c))) = [C c]` for each `c : Ω` |
| Supplied invertible K | `(K : X.Modules) [K.IsInvertible]` |
| Supplied identification on every fibre with the canonical adjunction line | `adj`: `SmoothMarkingFibreAdjunction`; fields `system : FlatLCIAdjunctionSystem p 1`, `normalized : system.IsNormalized`, `identification : K ≅ system.line (FlatLCIBaseChange.identity p)` |
| n arbitrary, including zero; sections; pairwise disjoint; relatively smooth | `(n : ℕ) (a : Fin n → (S ⟶ X))`, `ha : ∀ i, a i ≫ f = 𝟙 S`, `hdisjoint` on point-set ranges, `hsmooth : ∀ i, Set.range (a i) ⊆ f.smoothLocus` |
| D is the product of the section ideals | `smoothMarkingIdeal a := ∏ i : Fin n, (a i).ker`; this is an actual quasi-coherent ideal, not an assumed divisor |
| Effective Cartier and relative effective Cartier | `(smoothMarkingIdeal a).IsRelativeEffectiveCartier f`, the recorded conjunction of invertibility of the ideal and flatness of its closed subscheme over S |
| D is the finite disjoint union of copies of S, with its specified inclusion in X | `∃ e : (∐ fun _ : Fin n ↦ S) ≅ (smoothMarkingIdeal a).subscheme, e.hom ≫ ...subschemeι = Sigma.desc a`; `ha` makes it an isomorphism over S. A finite disjoint union of identity S-morphisms is finite flat |
| L = K tensor O(D), invertible | `smoothMarkingTwist K a := K ⊗ Scheme.Modules.dual (smoothMarkingIdeal a).toModules`, followed by `.IsInvertible` |
| Arbitrary base change | The `∀ (T : Scheme.{u}) (b : T ⟶ S)` clause: equality of the comap ideal with the product ideal of `f.baseChangeSection (a i) (ha i) b`; the latter is relative effective Cartier over T; a unique twist comparison is supplied |
| Canonical comparisons preserve tensor products of sections | `IsSmoothMarkingDualFrame` is a generator of the ideal with dual evaluation one. `IsSmoothMarkingTwistComparison` requires the formula on every local `s ⊗ t⁻¹`, using actual `tensorPullbackSection`; the target inverse frame evaluates to one on a generator whose inclusion is precisely `g#t` |
| Composition compatibility | `SmoothMarkingTwistComposition f K D`: for two cartesian family base changes and any normalized comparisons, the composite through `tensorPullbackSectionComp` and the literal `comap_comp` transport satisfies the same normalizing formula. The theorem's unique comparison clause identifies it with the direct comparison |
| Naturality for isomorphic families carrying K and markings | `SmoothMarkingTwistNaturality f K a`: arbitrary base isomorphism `q : S ≅ T`, curve isomorphism `e : X ≅ Y`, equality `e.hom ≫ p = f ≫ q.hom`, arbitrary `perm : Equiv.Perm (Fin n)`, marking equalities, and supplied line identification `kappa`; the unique twist comparison satisfies the same frame formula |
| Every reduced irreducible component and its normalization | The final universal clause takes any `[IsIntegral Z]`, closed immersion `i : Z ⟶ pullback f t`, and `Set.range i ∈ irreducibleComponents ...`; these specify exactly the reduced component scheme. Its normalization is the existing `Z.normalization` and its map to the fibre is `Z.fromNormalization ≫ i` |
| C is proper smooth connected curve | `SmoothMarkingNormalizationConclusion`: `IsProper (r ≫ p) ∧ Smooth (r ≫ p) ∧ IsConnectedCurve (r ≫ p)` |
| Genus is dim H1(O) | Uses recorded `(r ≫ p).genus` and explicitly asserts its equality with `@Scheme.arithmeticGenus Ω _ C ⟨r ≫ p⟩`, whose definition is `finrankH ... 1` |
| Reduced ambient branch divisor B and marking divisor M | Existential ideals `B M`, `B.radical = B`, `M.radical = M`, both `.IsInvertible`; exact support equalities `{z | r z ∉ p.smoothLocus}` and `r ⁻¹' (⋃ i, Set.range (a i))` |
| Two branches at a self-node | Explicit cardinality formula on `{z : C // r z = y}`: zero off this component, one if another component passes through y, otherwise two; this is the branch classification of the recorded normalization theorem |
| Branch and marking supports disjoint, finite, and Ω-rational | `Disjoint ...`, both `.Finite`, every support point closed and the range of a section `Spec Ω ⟶ C` of `r ≫ p` |
| Each marking occurs once | For each index i the preimage of its range has `Nat.card` equal to one if it meets the component and zero otherwise; reducedness of M records multiplicity one |
| Canonical normalization isomorphism | The component predicate provides `eb` with `IsNodalNormalizationAdjunctionComparison`, `em` with the marking dual-frame comparison, and `es` with `IsSmoothMarkingSumComparison`; the resulting `e` is exactly `pullback(e0) ≪≫ em ≪≫ ((pullback(adj.identification) ≪≫ eb) ⊗ᵢ refl) ≪≫ es`. Its target is `(r ≫ p).relativeDifferentials ⊗ dual (B * M).toModules`, literally Ω1 tensor O(B+M) |
| Degree formula | `@Scheme.Modules.degree Ω _ C ⟨r ≫ p⟩ ((tensorPullback r).obj L) = (2 * (r ≫ p).genus : ℤ) - 2 + B.support.ncard + M.support.ncard`; degree is the recorded Euler-characteristic difference |
| Agreement with divisor degree | For any presentation `N ≅ dual E.toModules ⊗ F.toModules` of an invertible module by the signed Cartier divisor E-F, its Euler degree is `(E.subschemeι ≫ r ≫ p).finrankΓ - (F.subschemeι ≫ r ≫ p).finrankΓ`. This is the usual effective-divisor degree difference, and includes F empty |
| n=0: empty D and M | Explicit `n = 0 → smoothMarkingIdeal a = ⊤`; the M support equality is the preimage of an empty union and hence empty, with radical ideal M=top |
| No K construction, positivity, stability, modification, smooth generic fibre | K and its fibre identifications are inputs; none of the prohibited extra assumptions or conclusions occurs |

The section and branch comparisons are retained as data with generator normalizations;
there is no choice from an unconstrained Nonempty isomorphism. The normalization iso e
is specified as the displayed composite of those maps. All local coordinate predicates
belong to this theorem's construction, rather than introducing separate mathematical notions.

### Dependency declarations read and used

The recorded signatures and docstrings were read in the library, including the full
`exists_flatLCICanonicalAdjunction` interface and `nodal_normalization_adjunction`.

| Dependency | Module | Recorded declaration |
| --- | --- | --- |
| `pqf-def-locnoeth` | `Mathlib.AlgebraicGeometry.Noetherian` | `AlgebraicGeometry.IsLocallyNoetherian` |
| `def-weil-proper-morphism` | `Mathlib.AlgebraicGeometry.Morphisms.Proper` | `AlgebraicGeometry.IsProper` |
| `def-weil-flat-morphism` | `Mathlib.AlgebraicGeometry.Morphisms.Flat` | `AlgebraicGeometry.Flat` |
| `def-sbc-locally-finite-presentation` | `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation` | `AlgebraicGeometry.LocallyOfFinitePresentation` |
| `def-weil-finite-type-morphism` | `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` | `AlgebraicGeometry.LocallyOfFiniteType` |
| `def-weil-quasi-separated-morphism` | `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated` | `AlgebraicGeometry.QuasiSeparated` |
| `def-sc-invertible-module` | `WeilConjectures.AlgebraicGeometry.Modules.Invertible` | `AlgebraicGeometry.Scheme.Modules.IsInvertible` |
| `lem-trf-flat-lci-canonical-adjunction` | `Sheaf.AlgebraicGeometry.FlatLCICanonicalAdjunction` | `AlgebraicGeometry.exists_flatLCICanonicalAdjunction` |
| `def-sbc-smooth-morphisms` | `Mathlib.AlgebraicGeometry.Morphisms.Smooth` | `AlgebraicGeometry.Smooth` |
| `def-pc-relative-effective-cartier` | `WeilConjectures.AlgebraicGeometry.RelativeEffectiveCartier` | `AlgebraicGeometry.Scheme.IdealSheafData.IsRelativeEffectiveCartier` |
| `def-pc-divisor-line-bundle` | `WeilConjectures.AlgebraicGeometry.EffectiveCartier` | `AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.isInvertible_dual_toModules` |
| `def-pc-module-pullback` | `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction` | `AlgebraicGeometry.Scheme.Modules.tensorPullbackSectionAdjunction` |
| `def-weil-pbc-reduced-normalization` | `Sheaf.AlgebraicGeometry.ReducedNormalization` | `AlgebraicGeometry.Scheme.reducedNormalization` |
| `def-sc-kahler-differentials` | `WeilConjectures.AlgebraicGeometry.Modules.Differentials` | `AlgebraicGeometry.Scheme.Hom.relativeDifferentials` |
| `def-pc-degree-line-bundle` | `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar` | `AlgebraicGeometry.Scheme.Modules.degree` |
| `def-weil-geometric-fibre` | `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback` | `CategoryTheory.Limits.pullback` |
| `def-weil-pure-dimension` | `Sheaf.AlgebraicGeometry.PureDimension` | `AlgebraicGeometry.Scheme.IsPureDimension` |
| `def-pc-reduced-scheme` | `Mathlib.AlgebraicGeometry.Properties` | `AlgebraicGeometry.IsReduced` |
| `def-weil-pbc-adic-completion` | `Mathlib.RingTheory.AdicCompletion.Basic` | `AdicCompletion` |
| `def-weil-pbc-multivariate-power-series` | `Mathlib.RingTheory.MvPowerSeries.Basic` | `MvPowerSeries` |
| `def-sc-genus` | `WeilConjectures.AlgebraicGeometry.Curve` | `AlgebraicGeometry.Scheme.Hom.genus` |
| `def-sfb-nodal-normalization-adjunction-comparison` | `Sheaf.AlgebraicGeometry.NodalNormalizationAdjunction` | `AlgebraicGeometry.IsNodalNormalizationAdjunctionComparison` |
| `def-sfb-flat-lci-adjunction-system` | `Sheaf.AlgebraicGeometry.FlatLCICanonicalAdjunction` | `AlgebraicGeometry.FlatLCIAdjunctionSystem` |
| `def-sfb-flat-lci-base-change` | `Sheaf.AlgebraicGeometry.FlatLCICanonicalAdjunction` | `AlgebraicGeometry.FlatLCIBaseChange` |
| `def-sc-normalization` | `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization` | `AlgebraicGeometry.Scheme.normalization` |
| `def-sc-curves` | `WeilConjectures.AlgebraicGeometry.Curve` | `AlgebraicGeometry.IsCurve` |
| `def-pc-genus` | `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar` | `AlgebraicGeometry.Scheme.arithmeticGenus` |
| `def-sc-local-free-generator` | `WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator` | `AlgebraicGeometry.Scheme.Modules.IsFreeGenerator` |
| `def-sbc-closed-immersion-ideal-sheaf` | `Mathlib.AlgebraicGeometry.IdealSheaf.Basic` | `AlgebraicGeometry.Scheme.Hom.ker` |
| `def-weil-pbc-scheme-reduction` | `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme` | `AlgebraicGeometry.Scheme.IdealSheafData.subscheme` |
| `def-nagata-invertible-ideal` | `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible` | `AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible` |
| `def-nagata-extended-ideal` | `Mathlib.AlgebraicGeometry.IdealSheaf.Functorial` | `AlgebraicGeometry.Scheme.IdealSheafData.comap` |

The inherited reduced-normalization import is retained. The component quantification
uses `Z.normalization` and `Z.fromNormalization` from `def-sc-normalization`, rather
than the general `reducedNormalization` construction; for integral Z these describe
the same reduced component normalization. Quantifying over integral closed component schemes avoids
choosing a second normalization or a different reduced structure. The supplied canonical
adjunction is specialized to the geometric fibre only; no global adjunction line or
Noetherian new base is assumed. Canonical pullback sections and composition use the
recorded `tensorPullbackSection`, `tensorPullbackSectionComp`, and section-normalized
adjunction. Divisor lines are exactly dual ideal modules, as their recorded declaration
specifies. The inverse frame uses the existing internal-Hom evaluation.

Stated proof-dependency modules are imported privately: the normalized branch adjunction,
Cartier criterion and pullback (RelativeEffectiveCartier and EffectiveCartier), dual/tensor
invertibility, monoidal pullback, point Cartier, smooth normality, perfect-field reduced
tensor and dense smooth locus. Mathlib properness, finite-presentation permanence,
Noetherianity, finite components, separated sections and residue-field results are imported
through their owning modules. `lem-sfb-curve-differential-euler-degree` and
`lem-trf-geometric-pure-fibre-point-dimension` have no recorded Lean module on the read
base, so there is no module to import for those proof-only future inputs. They are not
needed to type the statement and are named explicitly in the proof docstring.

### Searches and reuse audit

All searches ran with the prescribed `batch2/msearch.py Q41
lem-sfb-smooth-marking-normalization-twist` wrapper, together with `rg` in the exact
read-only library paths; no live source or compiler output was changed.

* LeanSearch, query `nodal curve normalization marked divisor canonical degree`: eight
  hits, including polynomial integral normalization and generic scheme normalization;
  none states the marking-twist theorem.
* LeanFinder, query `Disjoint smooth sections nodal normalization canonical twist`:
  eight generic Mathlib normalization hits (`normalizationCoprodIso`, its compatibility
  lemmas and `normalizationDiagramMap`); no marking or adjunction twist.
* Loogle, query `AlgebraicGeometry.Scheme.Modules.degree`: zero hits, unknown identifier
  in the Mathlib service. The recorded project EulerChar declaration was read directly
  and used instead.
* Mathlib grep, query `marking|nodal.*normalization|normalization.*nodal` in
  `AlgebraicGeometry`: zero hits.
* `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` for
  proposed declaration names: no collision. Search for this exact blueprint id in
  `lean/WeilConjectures`: no result.
* Concept searches found `MarkedNodalDualizingDegrees`, `NodalLogCanonicalReconstruction`,
  `LogCanonicalDeletionAlgebra`, `ElementaryContractionEvaluation`, and
  `NodalNormalizationAdjunction`. They were opened. The first constructs K and assumes
  a stable modification with integral Noetherian base and smooth generic fibre; the
  reconstruction theorem assumes projectivity and constructs a log-canonical
  polarization; deletion assumes genus at least two and connected nodal fibres.
  None is this proper-family theorem with supplied K and possibly disconnected fibres.
  `oldIdealX` is a product on a specialized contraction datum, and `nodalDeletionLine`
  uses the kernel of the disjoint-union map; neither is a general product-of-section-
  ideals interface on arbitrary disjoint sections. The theorem's product and line
  expressions are therefore named locally to its owning module as authorized helpers.
  The branch adjunction itself is reused verbatim.

### Sources and edge cases

Read the local Stacks sources `curves.tex` at `lemma-rr` (0BS6) and
`lemma-genus-smooth` (0C1A), and `divisors.tex` at
`lemma-section-smooth-regular-immersion` (067R). Temkin's unavailable source is not claimed
read: the ambient-branch comparison is precisely the recorded dependency's theorem.
The eight proof steps are reproduced, step by step, in the theorem docstring.

* n=0: Fin 0 is empty; the ideal is the empty product top, and M has empty support.
* Empty base: the fibre hypothesis is vacuous only because no geometric point exists;
  the other clauses still describe the unique line and empty marking scheme on the
  empty total space, with no nonempty component quantified in the last clause.
* Disconnected geometric fibres: no connectedness occurs in hfibres; connectedness is
  concluded only for the normalization of a single irreducible component.
* Smooth fibre: B is empty. A rational component with m markings gives -2+m, including
  negative or zero values; positivity is absent.
* Self-nodal cubic: normalization is P1, with two distinct branches, degree -2+2=0
  before markings. Two components meeting at one node contribute one branch on each.
* Components without markings: each marking-preimage cardinal is zero and M is empty;
  the degree formula retains just the ambient branches.
* Characteristic two: the completed local equation and field-compatibility equation use
  uv and no division by two. The branch normalization imports the signed comparison
  without imposing a characteristic restriction.
* Arbitrary/nonreduced/non-Noetherian new bases: the base-change clause has no such
  restrictions; ideal generators and dual evaluations are sheaf-module expressions.
* Universes: schemes and geometric fields use u consistently with the recorded
  geometric-fibre conventions, allowing all scheme-sized fields without introducing an
  independently smaller testing universe. All variables/universes are explicit and
  both auto-implicit settings are false.

Validation: prescribed scompile.py compiled the sandbox and named library module cleanly
(no warning), each below 60 seconds. Only the theorem proof is postponed. No global build,
local lake invocation, live file edit, or direct Git operation was used.

## Second reading by Q41

A separate clause-by-clause reading of the node and the complete module found and fixed
three drafting issues before delivery: the smooth-locus helper needed its explicit
locally-of-finite-presentation instance; the comparison composition needed to quantify
cartesian family base changes; and the family-isomorphism clause needed the base
isomorphism, family equation, and arbitrary marking permutation. The composite
normalization isomorphism is now an actual existential e constrained to the displayed
composite, and the degree/divisor comparison covers signed divisors, not only effective
ones. Classical decidability is scoped to the one definition with conditionals, so no
linter warning is suppressed. Reading the final file confirms every hypothesis and
clause in the table, the absence of connectedness on fibres, the actual product ideal,
the supplied (not constructed) K, and the n=0 clauses. This is the worker's second pass;
the maintainer performs the independent delivery review specified in the assignment.

## New nodes

`def-sfb-nodal-normalization-adjunction-comparison` attaches the exact landed
`AlgebraicGeometry.IsNodalNormalizationAdjunctionComparison` definition at
`Sheaf.AlgebraicGeometry.NodalNormalizationAdjunction:76`, using `existing: true`.
It defines the generator equation on smooth opens: an adjunction section identified
with da is sent to d(r#a) tensor the canonical dual-ideal section corresponding to
the ideal inclusion. The supplied objects are arbitrary; it neither assumes geometric
normalization hypotheses nor asserts existence of a comparison. The source is the
smooth-locus fundamental-class normalization (Stacks duality.tex, Tag 0E9Z) used by
the inherited nodal comparison (recorded Temkin §1.2(b)). I read the local Stacks
lemma; Temkin is still not claimed read. This is the same predicate, binder for binder,
including its quantification over every normalized smooth comparison and its
implication for each function a and adjunction section m. It also retains degree-one
exterior sections and the actual canonical tensor-pullback section maps. The ideal
need not be Cartier for the predicate to make sense: the dual and its distinguished
section exist for any supplied ideal. Empty opens give vacuous equations. No datum is
chosen and no proof or new Lean declaration is introduced.

Searches for this new node were made before attachment. LeanSearch query
`canonical normalization adjunction comparison on nodal curve determined by differentials on smooth locus`
returned eight generic normalization declarations, starting with `Scheme.Hom.fromNormalization`,
with no differential comparison. LeanFinder query
`normalization adjunction comparison nodal curve smooth locus differential divisor canonical section`
returned eight generic normalization declarations, starting with `Scheme.Hom.normalizationDiagramMap`.
Mathlib grep `IsNodalNormalizationAdjunctionComparison|[Nn]odal.*[Aa]djunction|[Aa]djunction.*[Nn]odal`
in AlgebraicGeometry returned zero hits. Exact declaration searches in WeilConjectures
and Mathlib returned no match; Sheaf found the existing definition and its theorem use.
DAG grep found it only in the theorem owner's record; `blueprint_refs.py search
'nodal normalization adjunction comparison'` returned zero nodes. The definition is
therefore reused rather than copied; a separate definition node supplies the missing
owner. The three wrapper search records are preserved verbatim in `mathlib_searches`.

## Returned-delivery repair H2

The independent review of immutable head `60b9a1c41b94` accepted the mathematics and
requested definition ownership. Added the new comparison node and cited it directly
from the item. Added all ten specified landed owners: `def-sfb-flat-lci-adjunction-system`,
`def-sfb-flat-lci-base-change`, `def-sc-normalization`, `def-sc-curves`, `def-pc-genus`,
`def-sc-local-free-generator`, `def-sbc-closed-immersion-ideal-sheaf`,
`def-weil-pbc-scheme-reduction`, `def-nagata-invertible-ideal`, and
`def-nagata-extended-ideal`. Their recorded declarations and source signatures/docstrings
were read; the dependency table records each module and name. The component curve uses
`IsConnectedCurve` (including dimension one), the genus equality uses `arithmeticGenus`,
local frames use `IsFreeGenerator`, and ideal operations use the actual kernel,
subscheme/radical, invertibility, and comap constructions. These were already the
Lean expressions; the repair supplies their missing DAG edges. The comparison node
has no dependency on the nodal-adjunction theorem, so the new ownership edge is acyclic.
Compared the retained node with the current shared main: its non-Lean fields matched
before these additive metadata repairs. The delivery wrapper rebases on current main.
The Lean source is unchanged from the independently reviewed version. This repair's
second worker pass read the new node against the complete definition, checked all
requested edges and the absence of additional geometric hypotheses. No independent
subagent review is claimed; the maintainer provides independent review.
