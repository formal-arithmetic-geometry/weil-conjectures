## Worker report

The module `Sheaf.AlgebraicGeometry.EquivariantComponentAffineGerms` states
`AlgebraicGeometry.Scheme.equivariant_component_affine_germs`, with its sole proof `sorry`.
The public abbreviation `AlgebraicGeometry.Scheme.componentAffineChart q V U` is the real
open `U ⊓ q ⁻¹ᵁ V`. It just names the intersection used throughout this node; it supplies
no structure or postponed data. Both declarations have source/blueprint docstrings.
The theorem docstring retains all seven proof steps and their named dependencies.

Hypothesis-by-hypothesis rendering:

| Node data or hypothesis | Lean |
| --- | --- |
| Schemes X and Z | `{X Z : Scheme.{u}}` |
| Finite index sets I, J | Independent types `Type v`, `Type w`, with `[Finite I] [Finite J]` |
| Open and closed subschemes X_i, Z_j | `U : I → X.Opens`, `T : J → Z.Opens`, with `hUc`, `hTc` asserting closedness; the open structure is carried by `Opens` |
| Disjoint decompositions covering each scheme | `hUd`, `hTd : Pairwise ... Disjoint ...`, and `hU : iSup U = ⊤`, `hT : iSup T = ⊤` |
| Integral subschemes | `[∀ i, IsIntegral (U i).toScheme]`, and the corresponding instance for T |
| Their generic points | `η : I → X`, `ξ : J → Z`, with `hη`, `hξ` asserting `IsGenericPoint` of the corresponding clopen subset in the ambient scheme |
| Finite morphism q | `q : X ⟶ Z`, `[IsFinite q]` |
| Component map φ, full component images and generic-point images | `φ : I → J`, `hqU : q '' U i = T (φ i)`, `hqη : q (η i) = ξ (φ i)` |
| Finite group acting by automorphisms and permuting components | `H : Type t`, `[Group H] [Finite H]`, `[MulAction H I]`, `a : H →* Aut X`, and `haU` |
| q invariant and φ invariant | `haq : (a h).hom ≫ q = q`, `hφ : φ (h • i) = φ i` |
| Fixed j with nonempty fibre O | `j : J`, `hO : Set.Nonempty {i : I \| φ i = j}`; the fibre index type is `{i : I // φ i = j}` |
| Nonempty affine open V inside Z_j | `V : Z.Opens`, `hVj : V ≤ T j`, `hV : IsAffineOpen V`, `hVn : Set.Nonempty (V : Set Z)` |

An open of the open subscheme Z_j is represented by its ambient open V, with `V ≤ T j`.
The open-immersion identification preserves affineness and sections, exactly as in the node's
first proof step. There is no assumption that all of Z_j is affine.

Conclusion-by-conclusion rendering:

| Node assertion | Lean |
| --- | --- |
| W = q⁻¹V, W_i = X_i ∩ W | `q ⁻¹ᵁ V` and `componentAffineChart q V (U i.val)` |
| W and every W_i are affine | `IsAffineOpen (q ⁻¹ᵁ V)` and the first component of the fibre-indexed conjunction |
| Each W_i nonempty, open and closed in W | `Set.Nonempty ...` and `IsClopen` of its inverse image along the subtype inclusion `W → X` |
| The W_i cover W | The displayed subtype-indexed `iSup` equals `q ⁻¹ᵁ V` |
| A and B_i are domains | `IsDomain Γ(Z, V)` and `∀ i : O, IsDomain Γ(X, componentAffineChart ...)` |
| Actual restriction is a ring isomorphism | Existential `e : Γ(X,W) ≃+* ((i : O) → Γ(X,W_i))`, with every `e s i` equal to `X.presheaf.map (homOfLE inf_le_right).op s` |
| Inverse pullback acts on W and sends B_i isomorphically to B_hi | `hρ`, `hβ` establish the required inverse-image inclusions; `Function.Bijective` of the actual `(a h⁻¹).hom.appLE` ring maps asserts they are isomorphisms |
| The restriction isomorphism is equivariant | `e (ρ_h s) ⟨h • i.val, ...⟩ = β_hi (e s i)` using the actual `appLE` maps; `hφ` supplies membership of the translated index in O |
| The composite a_i is injective | `Function.Injective (q.appLE V W_i inf_le_right)`; by definition `appLE` is `q.app V` followed by the actual restriction to W_i |
| Canonical germ identifications κ(ξ_j) = Frac A, κ(η_i) = Frac B_i | Two explicit `@IsFractionRing` propositions with algebra structures `(Z.evaluation V (ξ j) hξV).hom.toAlgebra` and `(X.evaluation W_i (η i.val) (hηW i)).hom.toAlgebra` |
| Residue map of q is the unique fraction extension | For every ring hom f, agreement on actual evaluations of all b in A iff f is the actual `q.residueFieldMap`, transported along `hqη` and `i.property` by `residueFieldCongr` |
| Its value on a fraction is a_i(b)/a_i(c) | The next clause states that formula for every `b c : Γ(Z,V)` with `c ≠ 0` |
| D_i consists of h fixing i | The final clause quantifies over all `h : H` and `hh : h • i.val = i.val`; this is exactly quantification over D_i, without a second stabilizer definition |
| Inverse-pullback action on κ(η_i) extends the B_i action to fractions | `hfix` gives `(a h⁻¹).hom (η i.val) = η i.val`, `hδ` gives its chart restriction, and the final equality computes the transported actual residue map on `eval b / eval c` as `eval (β b) / eval (β c)` for `c ≠ 0` |

The existential witnesses `hξV`, `hηW`, `hρ`, `hβ`, `hfix`, `hδ` are proofs of memberships,
inclusions and equalities forced by the hypotheses. They allow canonical maps to be typed;
no arbitrary map, ring action, or comparison is assumed. `Aut` multiplication is function
composition (`Aut_mul_def`), so the homomorphism `a` has the left-action convention and
inverse pullback has exactly the direction in the node. `Scheme.evaluation` is defined as
germ followed by residue. `IsFractionRing` uses localization at all nonzerodivisors, which
for the separately asserted domains are precisely the nonzero elements; its fraction
presentation and injectivity give the stated quotient-field notion and canonical injection.
The uniqueness clause gives the actual extension, and the stabilizer fraction formula
also determines its extension uniquely since these evaluations generate the fraction field.

Dependencies read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `Scheme.Hom`; also its actual `Hom.appLE`,
  `Hom.germ_stalkMap`, and `Hom.stalkMap_comp` interfaces.
- `def-pc-integral-scheme`: `Mathlib.AlgebraicGeometry.Properties`, `AlgebraicGeometry.IsIntegral`.
- `def-sc-generic-point`: `Mathlib.Topology.Sober`, `IsGenericPoint` (closure of singleton).
- `def-weil-finite-integral-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Finite`,
  `AlgebraicGeometry.IsFinite`. Only its finite branch is needed here.
- `def-weil-residue-field`: `Mathlib.AlgebraicGeometry.ResidueField`,
  `Scheme.residueField`, `Scheme.Hom.residueFieldMap`; the same module supplies the actual
  `Scheme.evaluation` and the canonical `Scheme.residueFieldCongr` transports.
- Proof-only dependencies are imported from their recorded Mathlib modules:
  `PrimeSpectrum.existsUnique_idempotent_basicOpen_eq_of_isClopen` (Prime.Topology),
  `IsAffineOpen.basicOpen` and `IsAffineOpen.isLocalization_basicOpen` (AffineScheme),
  `TopCat.Sheaf.isProductOfDisjoint` (PairwiseIntersections),
  `LocallyRingedSpace.Hom` (LocallyRingedSpace),
  `functionField_isFractionRing_of_isAffineOpen` (FunctionField),
  `Scheme.Hom.germ_stalkMap` and `Scheme.Hom.stalkMap_comp` (Scheme),
  `IsFractionRing.lift`, `lift_unique`, `lift_algebraMap` (FractionRing), and
  the scheme sobriety instances plus `IsGenericPoint.eq` (Properties and Sober).
  Scheme and FractionRing also occur in the statement, so their imports are public.

Source reading: local Stacks schemes.tex labels `lemma-standard-open-affine` (01I3),
`lemma-spec-sheaves` (01HV), algebra.tex `lemma-disjoint-decomposition` (00EE),
and morphisms.tex `lemma-integral-scheme-rational-functions` (01RV). Read the current
latest blueprint direct-images proof paragraph (3), the node's recorded ancestry, all
five statement dependencies and all proof dependencies with their declaration records.
There is no repair note for this item. The suggested CompactObject example is withdrawn
and contains no declarations; the current ProperReducedGlobalSectionsProduct module
provided the live header and docstring pattern.

Searches (prescribed `msearch.py Q98 lem-sfb-equivariant-component-affine-germs`):

- LeanFinder: “Finite invariant morphism of schemes with disjoint integral components,
  affine inverse image sections as equivariant product, generic residue field maps as
  fraction extensions”. Eight hits, including `Scheme.SpecToEquivOfField`, finite fibres,
  normalization identities, and `IsGaloisGroup.to_isFractionRing`; no combined statement.
- Loogle: `AlgebraicGeometry.Scheme.Hom.appLE, AlgebraicGeometry.Scheme.evaluation`.
  Zero hits for the pair.
- grep: `appLE|residueFieldCongr|evaluation` in `AlgebraicGeometry/ResidueField.lean`.
  Five hits, locating the actual evaluation definition; direct source reading also
  located the residue congruence and residue-map interfaces.
- LeanSearch: “Sections on finite disjoint integral components of a scheme form an
  equivariant product and generic residue maps are fraction field extensions”. Eight
  hits, including `Scheme.coprodPresheafObjIso`, `Scheme.residueField`,
  `functionField_isFractionRing_of_isAffineOpen`; these cover individual clauses.
- `rg` over `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` for
  `equivariantComponentAffine|component.*[Gg]erm|lem-sfb-equivariant-component-affine-germs`,
  followed by narrower searches for `componentAffineChart` and equivariant component
  affine charts. No duplicate of either declaration. `FiniteQuotientGenericFields`
  is the parent theorem with stronger quotient/normal/Noetherian hypotheses and a
  different conclusion, not a declaration of this node. Its proof discussion mentions
  the mathematics now isolated here. The generic-stalk and function-field files give
  individual comparisons but not this full equivariant statement.

Edge cases checked: singleton fibre, trivial group, two components exchanged by C₂,
nonfaithful action, arbitrary characteristic (including characteristic dividing |H|),
and finite nonflat maps. No freeness, normality, Noetherianity or flatness is assumed.
Empty I is incompatible with the explicit nonempty O hypothesis; empty schemes with
no possible selected component therefore create no omitted case. Components outside
O contribute no factor; no product action assumes transitivity of O. Independent
universe parameters u,v,w,t do not restrict scheme size or the finite index/group types.

Validation: every compiler invocation used the prescribed server-only `scompile.py`.
The first compile identified the explicit IsFractionRing argument order and a dependent
residue-field mismatch in the stabilizer formula. These were repaired by the correct
argument order and by typing the fixed-component restriction directly using `hδ`.
All variables/universes are explicit and `autoImplicit` is false. A subsequent reread
restricted the component inverse-pullback clauses to O, matching the node's scope.
No statement correction, new node or dependency repair is needed.

## Second reading by Q98

Worker self-check, performed in this thread with the node and final module open;
the maintainer supplies the independent delivery review. I compared the five
hypothesis groups (decompositions, generic points, finite map, invariant action,
selected chart) with their binders and checked each conclusion against the table.
In particular the product map has prescribed restriction coordinates, q's residue
map uses the inverse of the equality transport, and the stabilizer action uses h⁻¹
on both sections and residue fields. The fraction-ring algebra structures are the
actual evaluations. I removed the unnecessary outside-O scope of the component
pullback clause before the final compile. All theorem proofs remain `sorry`, and
the chart abbreviation has real data. No mismatch remains and no source statement
was changed.
