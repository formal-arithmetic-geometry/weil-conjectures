## Worker report

The module `Sheaf.Algebra.Homology.RelativePerfectHomFilteredColimit` states
`AlgebraicGeometry.relativePerfectHom_filtered_colimit`, with one `sorry`, and supplies
real constructions of its scalar-extension maps and ring objects. The node statement,
proof, and proof dependencies are unchanged. Its `stmt_deps` gains the already landed
`def-sfb-polynomial-koszul-diagonal-system`, solely to use its canonical general
scalar-extension composition identification. No independent new notion or node is needed.

Source read: `literature/stacks-project/more-algebra.tex`,
`lemma-colimit-relatively-perfect` (Tag 0DHX), especially (2) and its proof, and
`lemma-compute-RHom-relatively-perfect` (Tag 0E1U). The source agrees with the node:
only K is pseudo-coherent; L need not be pseudo-coherent or relatively perfect.

The hypothesis and conclusion correspondence is as follows.

- A small directed poset is `{I : Type u} [PartialOrder I]
  [IsDirected I (· ≤ ·)]`. The fixed `i₀ : I` implies nonemptiness, so a redundant
  `[Nonempty I]` hypothesis is unnecessary. The node explicitly says poset, so
  `PartialOrder` rather than the more general directed-preorder convention is used.
- The ring diagram is `F : I ⥤ CommRingCat.{u}`, and its chosen ring colimit is
  `colimit F`. The index and rings use the same universe, as required by the
  project's filtered-ring-colimit size convention. Colimit existence is inferred
  from the existing ring-category instance, not added as a hollow hypothesis.
- The homomorphism from R_i₀ to A_i₀ is the algebra structure of
  `A : CommAlgCat.{u} (F.obj i₀)`. Its hypotheses are exactly
  `[Module.Flat (F.obj i₀) A]` and `[Algebra.FinitePresentation (F.obj i₀) A]`.
  By `RingHom.flat_algebraMap_iff`, the first is precisely flatness of that map.
- The index tail is `Set.Ici i₀`. `relativePerfectRingAt F i₀ i` is the ring
  `F.obj i.val` under `F.obj i₀`, with structure map `F.map (homOfLE i.property)`.
  `relativePerfectRingLimit F i₀` is `colimit F` with structure map `colimit.ι F i₀`.
  The helper `relativePerfectBaseAlgebra` uses Mathlib's
  `commAlgCatEquivUnder.inverse`, retaining these specified structure maps.
- The rings A_i and A in the node are literally the tensor rings
  `A ⊗[F.obj i₀] relativePerfectBaseAlgebra T` for those under-ring objects T.
  This is the node's order of factors, A_i₀ first, regardless of the equivalent
  reversed order used in the Stacks text.
- `K L : DerivedCategory (ModuleCat.{u} A)` are the original K₀ and L₀ in D(A_i₀).
  `hK : DerivedCategory.IsPseudoCoherent K` uses the recorded bounded-above
  finite-free-representative definition, without strengthening it to perfectness.
- `hL` says `∃ a b : ℤ, a ≤ b ∧ DerivedCategory.torAmplitudeIn ... a b ...`.
  Its argument is L restricted to R_i₀ by the exact existing
  `(ModuleCat.restrictScalars (algebraMap (F.obj i₀) A)).mapDerivedCategory`.
  Unfolding the existing `torAmplitudeIn` tests the canonical derived tensor with
  every R_i₀-module in degree zero and vanishing outside [a,b]. Thus this is
  exactly the node's relative finite Tor interval, not Tor amplitude over A_i₀.
- `relativePerfectExtension A T` applies the recorded
  `relativeDualizingDerivedExtension` to tensor-algebra `includeLeft`. Its images
  of K and L are exactly K_i, L_i, K, L after derived extension in the node.
- `relativePerfectHomGroup A K L T` is the abelian group of morphisms between
  these two derived objects, formed with `AddCommGrpCat.of`.
- `relativePerfectTensorMap A f` is the actual tensor-algebra map induced by a
  map under R_i₀. `relativePerfectExtensionComp A f` uses
  `koszulDiagonalExtensionComp`; its normalization is uniqueness of left adjoints
  to the actual restriction-of-scalars functors. It is not a freely chosen
  isomorphism and assumes no flatness of the base-ring map.
- `relativePerfectHomMap A K L f` extends a morphism by the derived functor and
  conjugates by that canonical composition comparison. Its additive structure
  is obtained from the existing extension/restriction adjunction. Thus this is
  precisely derived extension on Hom, including nonflat transitions.
- The conclusion supplies a diagram `H : Set.Ici i₀ ⥤ AddCommGrpCat.{u}` and
  isomorphisms `e i` from its objects to the required Hom groups. Its first
  equation determines every transition: under e it is `relativePerfectHomMap`
  of `relativePerfectRingTransition F i₀ (leOfHom f)`. These are the specified
  ring transition homomorphisms from F, not arbitrary maps of Hom groups.
- The isomorphism `c : colimit H ≅ relativePerfectHomGroup ...` expresses the
  displayed isomorphism of abelian groups. The final equation determines `c.hom`
  on every colimit generator to be the actual scalar-extension map along
  `relativePerfectRingToLimit`, whose ring map is `colimit.ι F i.val`.
  The universal property therefore pins down the canonical homomorphism.
  Existentially packaging H and e only handles the functor laws in a statement
  with a sorry proof; it does not replace the canonical map by an arbitrary
  isomorphism or weaken the conclusion to an unnormalized Nonempty assertion.
- There is no hypothesis on flatness of transitions or colimit legs, no
  Noetherianity, and no perfectness of K. The finite presentation hypothesis on
  R_i₀ → A_i₀ is retained exactly as in the node, even though the model proof
  itself uses the weaker flatness assumption.

Dependency declarations read and used:

- `Mathlib.CategoryTheory.Limits.HasLimits`: `CategoryTheory.Limits.colimit`,
  `colimit.ι`, and the cocone/colimit universal property (the generated duals of
  the limit definitions). `colimit.w` constructs the under-ring legs.
- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`,
  `RingHom.flat_algebraMap_iff`, and `Module.Flat`.
- `Mathlib.RingTheory.FinitePresentation`: `Algebra.FinitePresentation`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, and `DerivedCategory.Q` (public through dependency imports).
  The existing Grothendieck-module instances supply the small-Hom derived category.
- `Sheaf.AlgebraicGeometry.AffineRelativeDualizingComparison`:
  `AlgebraicGeometry.relativeDualizingDerivedExtension`, the exact recorded
  K-flat derived extension, publicly imported through the diagonal system.
- `WeilConjectures.RingTheory.RingPseudoCoherent`:
  `DerivedCategory.IsPseudoCoherent`.
- Added landed dependency `Sheaf.Algebra.Homology.PolynomialKoszulDiagonalSystem`:
  `AlgebraicGeometry.koszulDiagonalExtensionComp`; its public data-module import
  supplies `koszulDiagonalExtensionAdjunction`. These are general constructions
  on commutative rings; their definitions impose no Noetherian, flatness, or
  polynomial-chart condition. A graph traversal checked that adding this edge
  does not create a dependency cycle.
- `WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude`:
  `DerivedCategory.torAmplitudeIn`, the existing K-flat-derived-tensor predicate.
- `Mathlib.Algebra.Category.CommAlgCat.Basic`: `commAlgCatEquivUnder`; the
  tensor algebra maps and preadditive composition maps are existing Mathlib data.

Recorded proof-dependency imports are ordinary, not public:
`WeilConjectures.RingTheory.FilteredColimitAlgebrasUnderlyingModule`
(`CommAlgCat.filtered_colimit_algebras_underlying_module`),
`WeilConjectures.Algebra.Homology.FilteredColimitsTensor`
(`SheafOfModules.filteredColimitsTensorComplex`),
`WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`
(`CategoryTheory.moduleSheaves_colimits_forgetful`), and
`Mathlib.Algebra.Category.Grp.AB` (filtered `colim.PreservesHomology`).
The other proof dependency `lem-sfb-relative-rhom-flat-base-change-model` currently
has no recorded module and is not imported; its proof input and naturality are
spelled out in the theorem docstring. It is not needed to TYPE this statement,
so this delivery does not state that separate theorem.

Edge cases checked against the source and the Lean signature: the tail contains
`⟨i₀, le_rfl⟩`; an empty I cannot have the node's specified i₀. A singleton or
constant diagram remains admitted. Zero rings, zero complexes, a = b, and arbitrary
integer degrees are admitted. No boundedness or finite-generation condition has
been added to L, and K need not be bounded below. Nonflat ring transitions and
nonflat colimit legs remain admitted. Identity and composite scalar maps are
normalized by the existing adjunction-based tensor identifications. All variables
and universe u are explicitly bound; `autoImplicit` is false.

Searches for existing declarations:

- `msearch.py ... leanfinder "Morphisms from pseudo coherent complexes to finite
  relative Tor amplitude complexes commute with filtered colimits of base rings"`:
  8 hits, including finite-presentation descent and underived Hom-colimit results;
  none states this varying-ring derived Hom continuity.
- `msearch.py ... loogle '"DerivedCategory", "colimit"'`: 0 hits.
- `msearch.py ... leansearch "Filtered colimit of derived Hom groups from a pseudo
  coherent complex with finite relative Tor dimension target"`: 8 hits, including
  `HomologicalComplex.instHasFilteredColimitsOfSize` and ordinary module/group
  filtered-colimit constructions; none is this statement.
- `msearch.py ... grep 'pseudo.?coherent|relatively.?perfect|colimit.*[Hh]om'
  Algebra/Homology`: 25 hits on complex colimits, homology, and colimit universal
  properties; none states the theorem.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for relative derived extension,
  Tor amplitude, scalar-extension composition, and Hom filtered colimits located
  the imported reusable interfaces above. Hom-colimit statements for fixed-ring
  sheaves and constructible coefficients have different hypotheses and objects.
  `grep -rn` for this node id in `lean/WeilConjectures` found no declaration.
  `rg` for each new `relativePerfect...` name in both libraries and
  `dag/lean_names_upstream.json` found none.

No statement correction, disputed statement, or dependency-interface repair is needed.

Validation: `scompile.py NO lem-sfb-relative-perfect-hom-filtered-colimit` compiled
both its sandbox probe and library module cleanly (3.8 s and 3.5 s). The initial
probe exposed an additive-instance inference issue and transparency in two under-ring
construction proofs; the final definitions use the actual adjunction's additive
instance and explicit cocone/map-composition equations.

## Second reading by NO

Performed a separate second pass over the unchanged node, source excerpt, and final
module after compilation. This is a self-review: the dispatcher explicitly forbids
starting another agent and assigns independent review to the maintainer.

The pass checked every binder: I is a small directed poset, i₀ supplies nonemptiness,
F is the ring diagram, A is flat finitely presented over its specified stage, K and L
are ordinary module derived objects, hK is pseudo-coherence over A, and hL is Tor
amplitude after restriction to the base ring. It then unfolded the base-algebra and
tensor-map definitions: they keep the actual F transition maps and chosen colimit
legs. The Hom transition uses derived extension with the adjunction-normalized
composition identification. H's objectwise e and its transition equation determine
exactly this diagram up to natural isomorphism, and c's equation determines the
canonical comparison on every generator. Thus no unnormalized arbitrary map or
stronger coefficient hypothesis has entered the statement.

The second pass also checked every helper has a source/blueprint docstring, data
are real constructions, only the main theorem is postponed, there are no file-local
instances or notations, and the new dependency edge is acyclic. The helper's local
`letI` lives inside its definition and merely supplies the additive structure of an
existing adjunction; it is neither statement-local notation nor a global new instance.
No additional mathematical mismatch was found; no node statement was changed.
