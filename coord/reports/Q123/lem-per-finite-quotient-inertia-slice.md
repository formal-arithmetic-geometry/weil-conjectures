## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteQuotientInertiaSlice` states
`AlgebraicGeometry.finiteQuotient_exists_pointedEtale_inertiaSlice` with one `sorry`.
It defines no new notion, proves nothing, and preserves the accepted statement and split.
The old worker ending concerned stage-1 re-splitting. The current node is split, reviewed
PASS by Q12, has no Lean record, and occurs as a stage-2 item in the queue. The current
brief-stage2 §0 explicitly authorizes its statement handoff. No repair note exists.

Source read: Stacks `pione.tex`, Tag 0BST, `lemma-inertia-invariants-etale`, including
its full proof: flat invariants, pointed etale product separation, equivariant clopen
refinement, and projection of the invariant algebra to the selected factor. The accepted
node supplies the normal generically free specialization and its ten-step proof including
strict localization, with comparison to ILO VI after 3.5, p.74. The latest blueprint
ancestor proof `lem-per-artin-gabber-affine-curve.proof.md`, Step 3, was also consulted.
The Lean docstring reproduces all ten accepted proof steps and their dependency uses.

Hypothesis and conclusion correspondence:

| Node text | Lean rendering |
| --- | --- |
| Y regular Noetherian | `[IsNoetherian Y]`, `hY : IsRegularScheme Y` |
| X normal Noetherian, without irreducibility | `[IsNoetherian X]`, `hX` gives `IsDomain` and `IsIntegrallyClosed` on every stalk; no integral hypothesis on X |
| finite group acting on X | `{G : Type v} [Group G] [Finite G]`, `a : G →* Aut X` |
| finite surjective quotient over Y | `q`, `[IsFinite q]`, `[Surjective q]`, `hinvariant` |
| invariant structure sheaf | `hsheaf`: injective actual section pullback, with image precisely the sections whose pullbacks by the action equal restrictions on every common subopen |
| orbit geometric fibres | `hgeometric`: every two geometric lifts over the same base point differ by an element of G; the reverse implication follows from `hinvariant` |
| generically free on a dense invariant open | `hfree`: a dense `U : X.Opens`, invariant under every action morphism, and trivial stabilizers for all geometric points of U |
| fixed geometric point over bar y | `barX : Spec (.of Ω) ⟶ X`, `[Field Ω] [IsAlgClosed Ω]`; bar y is explicitly `barX ≫ q` |
| H is its geometric stabilizer | `H : Subgroup G`, `hH : ∀ g, g ∈ H ↔ barX ≫ (a g).hom = barX`; this is a parameter identified with the exact stabilizer, not an arbitrary subgroup assumption |
| every prescribed pointed etale neighbourhood | arbitrary `T₀ : Scheme.PointedEtaleNeighborhood (barX ≫ q)` |
| pointed affine etale refinement | existential T, r, barT; `IsAffine T`, `Etale r`, `barT ≫ r = T₀.2.left`; composition with the etale map of T₀ gives T over Y |
| T integral regular Noetherian | `IsIntegral T ∧ IsRegularScheme T ∧ IsNoetherian T` |
| V affine normal integral Noetherian | `IsAffine V ∧ IsNormalScheme V ∧ IsNoetherian V`; the recorded `IsNormalScheme` includes `IsIntegral V` |
| H-action on V, equivariant pointed etale v | `b : H →* Aut V`, `Etale v`, `barV ≫ v = barX`, and `(b h).hom ≫ v = v ≫ (a h.val).hom` |
| finite surjective p and commutative square | `IsFinite p ∧ Surjective p`, `barV ≫ p = barT`, `v ≫ q = p ≫ r ≫ T₀.1.hom` |
| p is an H-quotient | `(b h).hom ≫ p = p`, the geometric-lift orbit clause for H, and the same sectionwise invariant-sheaf formula for p |
| H acts faithfully on V | `Function.Injective b` |
| every dense open U where q is etale | universal `U : Y.Opens`, `Dense (U : Set Y)`, `Etale (pullback.snd q U.ι)` |
| induced connected finite etale H-torsor | `c : Scheme.GaloisCoverAction H (pullback (r ≫ T₀.1.hom) U.ι)`, `ConnectedSpace c.Z`, cover isomorphism e to the iterated pullback `V ×_T (T ×_Y U)`, equation for c.π, and equation identifying c.smul with b after projection to V |
| torsor is simply transitive in every geometric fibre | the recorded `GaloisCoverAction.simply_transitive` field; its finite, etale and surjective fields concern the actual cover identified by e |
| conditional invertibility | `IsUnit (Nat.card H : X.residueField (barX (IsLocalRing.closedPoint Ω))) → IsUnit (Nat.card H : Γ(T, ⊤))`; since T is affine this is invertibility on T |
| R and C are the original strict local rings | `Scheme.strictHenselizationRing (barX ≫ q)` and `Scheme.strictHenselizationRing barX`, with the recorded construction |
| pointed maps identify strict local rings of T,V | `IsIso (Scheme.strictHenselizationMap (r ≫ T₀.1.hom) barT)` and `IsIso (Scheme.strictHenselizationMap v barV)`; their targets identify with the original points by the displayed pointing equations |
| C finite normal local over R | existential `IsLocalRing` structures for R,C; `IsDomain C`, `IsIntegrallyClosed C`, `(strictHenselizationRingMap q barX).Finite`, and `IsLocalHom` for the same map |
| induced faithful H-action on C | existential monoid hom β to ring automorphisms, `Function.Injective β`, with each β h required to equal `strictHenselizationRingMapEq` of the original inverse-action automorphism; inverse pullback gives the left ring action |
| canonical identification R = C^H | injectivity of the actual `strictHenselizationRingMap q barX` and the elementwise equivalence between its image and `∀ h, β h c = c` |
| no boundary, X regularity, excellence, or invertibility of G | no such binders or hypotheses; group cardinal invertibility occurs only as the antecedent of its conditional conclusion |

The iterated pullback in the torsor clause is canonically `V ×_Y U` because the preceding
square gives the structure map from V to Y. The equations on c.π and its action prevent
replacing this cover or action by an unrelated torsor. The categorical quotient field of
the existing Galois-cover interface is the usual equivalent torsor quotient formulation,
not an additional hypothesis. Connectedness includes nonemptiness. All maps in the
strict-local ring clauses are the existing canonical pointed maps, not arbitrary ring maps
chosen merely to have invariant images.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`
  is exactly `IsLocallyNoetherian X ∧ IsRegular X`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`
  and `IsNoetherian` (local Noetherianity plus compactness).
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`,
  together with the recorded `IsDomain` stalk formula for normality.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; geometric points are inline.
  `Scheme.SpecToEquivOfField` in `Mathlib.AlgebraicGeometry.ResidueField` confirms the
  interpretation of the underlying point and its residue embedding.
- `WeilConjectures.AlgebraicGeometry.NormalScheme`: `AlgebraicGeometry.IsNormalScheme`
  and `AlgebraicGeometry.Scheme.GaloisCoverAction`; all fields of the latter were read.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, `pullback.fst`,
  `pullback.snd`, through the scheme limits import.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `WeilConjectures.AlgebraicGeometry.StrictHenselization`: `Scheme.strictHenselizationRing`
  and `Scheme.strictHenselizationScheme`, defined by the small pointed affine colimit.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization`:
  `Scheme.PointedEtaleNeighborhood`, from the dependency's closed upstream audit.
- `Sheaf.AlgebraicGeometry.StrictHenselizationCanonicalMap`: `Scheme.strictHenselizationMap`,
  the unique structural and evaluation-compatible map; exposed by the ring-map import.
- `Sheaf.TraceFormula.StrictHenselizationTensorFinite`: the existing global
  `strictHenselizationRingMap` and `strictHenselizationRingMapEq`.
- `Mathlib.CategoryTheory.Endomorphism`: `Aut`; its multiplication is reverse categorical
  composition, so a monoid hom to Aut expresses the required left scheme action.

Imports of stated proof dependencies are retained as non-public imports, including the
finite-splitting, geometric-point, transitive-product, normal-component, strict-local
comparison and Noetherian/permanence modules. The partially attached flat-invariants
record lists declarations without a module: their source was found in
`WeilConjectures.Mathlib.RingTheory.TotallySplit`, and this module is imported privately.
Mathlib's invariant prime-orbit/residue interfaces occur in `Invariant.Basic` and
`Invariant.Galois`, both imported privately. No dependency record needs repair.

Edge cases checked before writing:

- Empty X or Y is excluded only by the specified geometric point and finite surjectivity,
  not by a global irreducibility assumption. Disconnected normal X and regular Y are allowed.
- H = 1 is allowed; Nat.card H = 1 makes the unit clause automatic, while the torsor can
  be a degree-one connected cover.
- In Z[i]/Z at 3, the geometric stabilizer is trivial although the ordinary decomposition
  group has order two. `hH` fixes the Ω-point, so does not incorrectly use that larger group.
- Wild ramification at 2 in Z[i]/Z and the characteristic-p translation action on A¹
  impose no invertibility restriction. The final conditional can have a false antecedent.
- Empty U cannot be dense in Y in the pointed setting; nevertheless the universal clause
  is an implication and does not assume an arbitrary dense open is nonempty separately.
- A nonempty dense open meets the etale image of T, explaining nonemptiness and connectedness
  of the restricted integral V without requiring U to contain the specified point.
- A generic Ω may be larger than the residue separable closure. No residue field is
  identified with Ω; the canonical small strict-henselization construction is used.
- Group universe v is independent of scheme universe u; all geometric test fields use u,
  as in the recorded geometric-point and strict-henselization interfaces. No equality
  between unrelated site universes is imposed. `set_option autoImplicit false` enforces
  explicit binding of all variables and universes.

Searches actually run, 2026-10-24:

- `msearch.py ... leanfinder` query “Finite group quotient of normal scheme admits pointed
  etale local slice for stabilizer of geometric point with strict henselization invariants”:
  eight results, invariant-ring stabilizer surjectivity and abstract Galois-category
  quotient-stabilizer results, no scheme inertia slice.
- `msearch.py ... loogle` query
  `AlgebraicGeometry.Scheme.GaloisCoverAction, AlgebraicGeometry.Scheme.strictHenselizationMap`:
  zero results, unknown identifier GaloisCoverAction in its Mathlib search environment.
  This is not treated as evidence that the project notion is absent; its source was read.
- `msearch.py ... leansearch` query “finite quotient scheme inertia group etale neighborhood
  slice”: eight results (ideal inertia, ramification, small etale site), no exact statement.
- `msearch.py ... grep` query `inertia.*slice|inertia.*invariant|geometric.*quotient`,
  Mathlib `AlgebraicGeometry`: zero hits.
- Local `rg` in Mathlib, `lean/WeilConjectures`, `lean/Sheaf`, and the upstream-name index
  for `inertia.?[Ss]lice|[Qq]uotient.?[Ii]nertia`: no exact statement; related invariant
  and inertia theorems are ring-theoretic. Exact node-id search in WeilConjectures: no hit.
- Broader local concept searches for invariant sheaves, geometric orbit fibres, generically
  free actions and canonical strict-local maps located NormalScheme, FiniteQuotientGenericFields,
  AdmissibleFiniteSchemeQuotient and StrictHenselizationCanonicalMap. The generic-fields lemma
  has a different conclusion. AdmissibleFiniteSchemeQuotient has extra admissibility/topology
  packaging, so its definition is not substituted for the precise inline hypotheses.

No new nodes, dependency repairs, statement correction, or disputed statement.

Validation: the prescribed server scompile.py accepted the module in both sandbox and library
contexts. deliver2.py --no-push then recompiled the final module and reported:
“OK (dry run): commit aa8fbb09bb0 passes the preflight and compiles; nothing pushed”.
No compiler errors or unexpected warnings were reported.

## Second reading by Q123

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
