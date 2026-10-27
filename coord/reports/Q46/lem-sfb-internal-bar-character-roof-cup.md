## Worker report

The module `Sheaf.CategoryTheory.InternalBarCharacterRoofCup` states
`CategoryTheory.CondensedDerivedRestriction.internalBarCharacterRoofCup`, with its
only proof postponed by `sorry`. Its data definitions are actual composites and
finite recursions. No node statement is corrected and no dependency is replaced.

Clause-by-clause correspondence:

- An arbitrary commutative condensed ring is `A : CondensedBar.Ring.{u}`: the
  existing `CommMon` of abelian sheaves on the coherent `Profinite.{u}` site. The
  underlying ring is `A.toMon`, the recorded `Profinite.CondensedRing`. Internal
  modules are the existing `CondensedBar.Modules A`, hence Mathlib `Mod`; internal
  equivariant modules are the existing `CondensedBar.Equivariant A G`, hence
  `Profinite.CondensedAction.ActionModule A.toMon G`. There is no requirement of a
  topological presentation of A or of a constant coefficient ring.
- `G : Type u`, `Group`, `TopologicalSpace`, `IsTopologicalGroup`, `CompactSpace`,
  `T2Space`, and `TotallyDisconnectedSpace` say that G is profinite. Its action
  category uses C(S,G) on every profinite test object, with base-change naturality.
  Universes are explicitly bound; section coefficients and morphisms use u+1,
  categories have objects in u+2, and the existing ordinary derived category
  localization has morphisms in u+1, exactly the dependency convention.
- `R : InternalBar.Resolution A.toMon G` is the normalized free homogeneous
  resolution, not an arbitrary complex: `freeIso`, `diagonal`,
  `boundary_generator`, and `augmentation_generator` specify all its formulas.
  `CondensedBarRoof.complex R` places P_n in degree -n, with zero positive terms
  and ordinary signed cochain shifts.
- `e : RoofAugmentation R`, `augmentationEquation R e`, and `[QuasiIso e]`
  specify the augmentation as a cochain map. Its quasi-isomorphism property is
  the bar-resolution exactness, already supplied by the roof-adjunction node;
  it is not an extra hypothesis on A, G, characters, or bar projectivity. The
  conclusion holds for every representative satisfying this normalization,
  rather than selecting any arbitrary morphism from an existence theorem.
- `coefficient A G` is A[0] with trivial action; `cohomology A G` is C=RΓ_G(A[0]).
  `inflationPhi`, `inflationGradedCup`, `cupUnit`, and `baseUnitIso` are the
  existing canonical invariant-inclusion derived adjunction and lax monoidal cup.
- The existential `t : ℕ → ℕ → ℤ` is outside the quantification over A, G,
  characters and lifts. Its first clauses say t is ±1 with both zero-degree
  values +1. The next clause is exactly the dependency's ordered graded identity:
  cup(Phi_p(x),Phi_r(y))=t_(p,r) Phi_(p+r)(y[p] after x), with Mathlib
  `ShiftedHom.comp` retaining canonical shift addition and the indicated order.
- `Character A G` is the existing natural additive condensed-group map. The
  existing `extension a`, `extensionSequence a`, and `extensionExact a` have
  the specified action (x+a(g)y,y), first-coordinate inclusion, and
  second-coordinate projection. `(extensionExact a).singleδ` is its canonical
  Mathlib short-exact-sequence triangle boundary; it has the cone normalization
  specified by the roof-adjunction dependency.
- An arbitrary allowed cochain lift is `L : complex R ⟶ (complex R)⟦1⟧`.
  `characterLiftComponent` moves its degree -1 component through the canonical
  bar-term and shift identifications, then applies R.augmentation.
  `IsCharacterLift R a L` says on every S and every two-tuple x that its value
  on `InternalBar.basis ... x` is a(x₀⁻¹x₁). This is an equality on internal
  generalized generators, never an assumption that sections are free modules.
- `characterRoof R e q F` is precisely inv(Q(e)) followed by Q(F followed by
  e[q]), with the existing Q/shift and singleFunctor/Q comparisons displayed.
  In mathematical right-to-left notation it is Q(e[q]F)Q(e)⁻¹.
- The first pair of conclusions is `characterRoof R e 1 L =
  -(extensionExact a).singleδ` and
  `inflationPhi A G 1 (characterRoof R e 1 L) = -characterClass a`.
  The character class is the existing positive unipotent connecting class,
  not a class defined by the roof itself.
- The general clause quantifies over every `q : ℕ`, every character family
  `a : Fin q → Character A G`, every lift family L, and precisely the
  component equations `∀ i, IsCharacterLift R (a i) (L i)`. No lift uniqueness,
  homotopy comparison, or existence assertion is added as a hypothesis.
- `orderedCharacterLift` composes L₁, then shifted L₂, etc., using canonical
  `ShiftedHom.comp`. `orderedCharacterRoofs` composes their derived roofs in
  the same order. Their equality is the first general conclusion. Both specialize the generic
  `orderedShiftedArrows` recursion, which avoids costly repeated elaboration
  of the action-category instance inside a dependent recursion.
- `orderedCharacterCup` starts with the actual unit and appends each positive
  `characterClass` using the existing ordered binary graded cup. Its equality
  to `((-1 : ℤ)^q * characterCupSign t q) • inflationPhi ...` is the second
  general conclusion. `characterCupSign` has T₀=T₁=1 and the stipulated
  T_(q+1)=T_q t_(q,1) for q≥1.
- At q=0 both composites are identity, with the zero-shift isomorphism made
  explicit by `ShiftedHom.mk₀`, and the empty cup is the unit with its
  canonical regular-unit comparison. No projectivity, acyclicity of underived
  Hom, or exactness of global sections occurs anywhere in the statement.

Dependency declarations read and used:

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing` (reexported).
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, `Mod.regular`.
- `Sheaf.CategoryTheory.CondensedActionModule`:
  `Profinite.CondensedAction.ActionModule`, `Modules`, and `sectionModule`.
- The size-convention node is metatheoretic, with no declaration to import;
  explicit universe u and the dependency's category sizes implement it.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `DerivedCategory.Q`, and `DerivedCategory.singleFunctorIsoCompQ`.
- `Sheaf.CategoryTheory.CondensedInternalBarResolution`:
  `Profinite.CondensedAction.InternalBar.Resolution`, `basis`, `onSections`.
- `Sheaf.CategoryTheory.InternalBarRoofAdjunction`:
  `CategoryTheory.CondensedBarRoof.complex`, `termIso`, `single`,
  `RoofAugmentation`, `augmentationEquation`; the proof plan uses
  `normalized_roofs` and its `extensionEquation`.
- `Sheaf.CategoryTheory.InternalInflationGradedCup`:
  `CategoryTheory.CondensedDerivedRestriction.inflationPhi`,
  `inflationGradedCup`, `internalInflationGradedCup`, `inflationPhiIdentity`.
- `Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus`:
  its public `CondensedUnipotentClass` import supplies `Character`,
  `extensionExact`, `characterClass`; its reexported `CondensedDerivedCup`
  supplies `coefficient`, `cohomology`, `cupUnit`, `baseUnitIso`.
  The proof uses the normalization and exactness specified in this node.

The two public imports reexport every statement dependency and every stated
proof dependency. Helpers belong to this same node and are listed in its
lean.declarations. No new independent mathematical notion or definition node
is required. The source's current `latest` direct-images proof paragraph (3)
was opened: it supplies the open-direct-image context, not a published proof
of this auxiliary normalization. The module honestly retains the node's
agent-formulated five-step proof instead of attributing it to that paragraph.

Edge cases checked before writing: q=0 (empty Fin 0 families, both identities,
cup unit, T₀=1); q=1 (single roof, negative connecting class, T₁=1); zero
character (split extension, zero boundary); trivial group (only zero additive
character); zero ring (all relevant morphisms zero, still the same universal
integer signs); characteristic two (negative equals positive, without dividing
by 2). Noncommutative G is permitted: a(g₀⁻¹g₁)=a(g₁)-a(g₀) only uses the
additive character law. No mathematical defect or disputed statement found.

Searches made with the prescribed wrapper and direct source search:

1. LeanFinder: `Internal condensed character extension boundary bar resolution
   roof ordered cup product`. Eight Dold--Kan functor hits, none the assertion.
2. Loogle: `ShiftedHom.comp, DerivedCategory.Q, ShortComplex.ShortExact`.
   No hits; service reported unknown identifier ShiftedHom.comp. Read its actual
   Mathlib source directly, where the declaration does exist.
3. LeanSearch: `Bar resolution character extension connecting morphism cup
   product`. Eight hits: Rep.barResolution, Rep.barComplex, its differential,
   Rep.barResolution.extIso, ordinary groupCohomology.δ, and a generic injective
   resolution helper. Ordinary discrete representations and projective Ext do
   not state the internal condensed character roof/cup theorem.
4. msearch grep in CategoryTheory: `character.*[Rr]oof|[Rr]oof.*[Cc]haracter|
   inflationGradedCup`; no existing theorem. Direct rg of WeilConjectures and
   Sheaf with the same query located only the graded-cup dependency plus
   unrelated character/roof prose. The explicit node-id grep in
   lean/WeilConjectures found nothing. Exact new-name search across both library
   roots and Mathlib found no duplicate declaration.

## Second reading by Q46

A second pass by the same dispatched worker (no other agent was started,
following the explicit launcher instruction). The independent mathematical
review remains the maintainer's review of the delivery; this paragraph does
not claim another person's review.

Reopened the node and the complete module and checked all four displayed
conclusions, each binder, and the order of every composite. In particular,
checked that IsCharacterLift uses x₀ inverse times x₁, the boundary is the
existing canonical singleδ with an external minus sign, Phi uses the existing
shifted derived adjunction, and [a] is independently defined from the
extension. Checked that t is quantified before A and G and the finite-family
clause uses the same t as the binary cup identity. The empty cup and both
empty composites retain their zero-shift identifications. The augmentation
normalization is the existing augmentationEquation, not an arbitrary
quasi-isomorphism. Recursion is left-associated in cup order and appends the
last shifted roof, so no characters are commuted. No node correction, new
node, dependency interface change, or omitted clause was needed.

Validation: the final full module compiled cleanly through scompile.py in both
sandbox and library mode (20.3 s and 19.9 s). An initial syntax issue was fixed;
a subsequent 60-second timeout was diagnosed by a reduced diagnostic compile
and repaired by elaborating the shifted-composition recursion generically.
No time limit was raised and no diagnostic source is delivered.
