## Worker report

The module `Sheaf.Algebra.Homology.CompleteLocalCoherentDuality` states
`DerivedCategory.complete_local_coherent_duality`, with its sole proof `sorry`.
It also gives two real constructions belonging to this statement:
`completeLocalDualFunctor R Ω` is the recorded RHom bifunctor with fixed second
argument Ω, and `completeLocalBidual R Ω K` is the transpose of evaluation after
the Koszul interchange. Neither construction chooses a map or a closed structure.
The latter uses the existing representative-normalized `SignedRingedHom.adjunction`.
No statement correction, disputed statement, dependency repair, or new node is needed.

Hypotheses and clauses, individually:

- A commutative ring is `(R : Type u) [CommRing R]`.
- Noetherianity is `[IsNoetherianRing R]`, exactly the recorded dependency definition.
- Locality and its unique maximal ideal are `[IsLocalRing R]` and
  `IsLocalRing.maximalIdeal R`. The local-ring class includes nontriviality.
- Completeness is `[IsAdicComplete (IsLocalRing.maximalIdeal R) R]`.
  `AdicCompletion.of_bijective_iff` identifies this with bijectivity of the
  canonical map to the inverse limit. Including n=0 adds the zero quotient and
  does not change the inverse limit indexed by n>=1 in the node.
- The ordinary module derived category is `DerivedCategory (RingSiteModules R)`,
  with its usual chosen small Hom universe `[HasDerivedCategory.{u} ...]`.
  `RingSiteModules` is the existing module sheaf category on `Discrete PUnit`
  with bottom topology and constant ring R. Evaluation at its unique object is
  the ordinary R-module interpretation: the site has no nonidentity arrows or
  nontrivial covering conditions. This is also the parent's existing encoding.
- RHom is precisely `SignedRingedHom.homFunctor`, whose data are
  `derivedInternalHomOfUniverses.{u,u,u,u}` from the recorded dependency.
  The helper uses `Prod.sectL ... Ω` to fix the second variable, so it is
  contravariant in K, not in Ω.
- D_fg is Mathlib's `ObjectProperty.FullSubcategory` of the inline predicate
  `∀ i : ℤ, Module.Finite R (((homologyFunctor ... i).obj K).val.obj (op ...))`.
  This predicate has no upper or lower bound. It is not replaced by perfect,
  pseudo-coherent, or bounded coherent objects.
- Existence of Ω is `∃ Ω : DerivedCategory (RingSiteModules R)`.
- Ω has finite cohomology by the first conjunct, in every integer degree.
- Ω is bounded by `∃ a b : ℤ, ∀ i, i < a ∨ b < i → IsZero (H^i Ω)`.
  Requiring a<=b is unnecessary for a vanishing-interval witness; every such
  witness can be enlarged, including when Ω=0.
- The anti-equivalence is the existential `e : D_fgᵒᵖ ≌ D_fg`.
  Its functor after the full-subcategory inclusion is naturally isomorphic to
  the opposite inclusion followed by `completeLocalDualFunctor R Ω`.
  This compatibility fixes the actual RHom action on morphisms, as well as on
  objects; an arbitrary equivalence of the category is not the conclusion.
  In particular RHom(K,Ω) is coherent whenever K is coherent, since it is
  isomorphic to the included coherent object given by e.
- The D+/D- exchange is given by the two displayed equivalences between
  existence of a lower vanishing bound on K and an upper bound on D(K), and
  existence of an upper bound on K and a lower bound on D(K). Together with
  the anti-equivalence these give the restrictions in both directions.
- Preservation of Db is the explicit third, two-bound implication for K and D(K).
- Canonical biduality for EVERY coherent K is `IsIso (completeLocalBidual R Ω K)`.
  The helper is `(adjunction D(K)).homEquiv K Ω` applied to the composite
  `K ⊗ D(K) --braiding--> D(K) ⊗ K --counit--> Ω`. This is the canonical
  evaluation transpose required by the node, not a bare existence of an iso.
- Naturality in K is the final equality for all coherent K,L and every f:K→L:
  `f ≫ δ_L = δ_K ≫ D.map (D.map f.op).op`. Both contravariances are present.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` and its ideal-fg meaning.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, and `DerivedCategory.Q`; cohomology is
  `DerivedCategory.homologyFunctor`, in `...DerivedCategory.HomologySequence`.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `CategoryTheory.derivedInternalHomOfUniverses`, including the K-injective
  representative comparisons and two-variable quasi-isomorphism invariance.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite` (top submodule FG).
- `Sheaf.Algebra.Homology.RingHomExtensionDefs`: `CategoryTheory.RingSiteModules`.
  Its constant ring sheaf is the existing `CochainComplex.onePointRingSheaf`
  from `Sheaf.Algebra.Homology.KFlatTensorQuasiIso`.
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses` publicly reexports
  `...RingedInternalHomSignedCalculus`: `SignedRingedHom.homFunctor`,
  `SignedRingedHom.adjunction`, its `normalizedAdjunction_existsUnique`, and
  the ordinary derived tensor and braiding. The source fixes the adjunction
  by actual K-flat total tensor and ordinary evaluation, with no arbitrary choice.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `IsAdicComplete` and
  `AdicCompletion.of_bijective_iff`.

The last three DAG dependencies were already recorded and landed; they are added
at the end of stmt_deps to name the existing module-site, canonical adjunction,
and completeness interfaces used. All original dependencies are retained.
No dependency node is edited. The module uses Mathlib `ObjectProperty.FullSubcategory`
and `ObjectProperty.ι` directly and introduces no second coherent-category definition.

Proof imports: the recorded Cohen presentation, Noetherian pseudo-coherence criterion,
Hom complex, and Mathlib `CochainComplex.isKInjective_of_injective` are imported.
The four new algebraic proof prerequisites (regular-local bounded injectives,
finite-map transfer, coherent RHom finiteness, and finite-injective evaluation)
have no Lean records in the base; there is consequently no recorded module to
import for them. They are cited individually in the complete eight-step theorem
docstring, and no missing proof prerequisite is made an extra hypothesis.

Sources opened: local `literature/stacks-project/dualizing.tex`,
lemma-ubiquity-dualizing (0BFR), complete-local case and proof, and lemma-dualizing
(0A7C), including its statement on the unbounded coherent category and its
canonical evaluation proof. The eight-step docstring follows the entire DAG
proof, including scalar-action normalization, canonical-map identification,
naturality, and both degree-bound calculations.

Edge cases checked:

- A field is complete for its zero maximal ideal; Ω=R[0] gives degreewise
  finite-dimensional duality, even on a complex with nonzero cohomology in
  every degree. No boundedness is accidentally imposed on K.
- Complete DVRs and nonregular Artinian local rings are included. The conclusion
  does not claim Ω=R[0] or perfectness, and imposes no Gorenstein condition.
- K=0 and zero cohomology at arbitrary degrees satisfy the finiteness predicate
  and all relevant vanishing bounds. No nonzero object hypothesis is added.
- The zero ring is excluded by `IsLocalRing`, agreeing with a ring having a
  unique maximal ideal (which is proper). No characteristic restriction occurs.
- For J supported in [a,b], K bounded above by c gives D(K) supported below by
  a-c; K bounded below by c gives D(K) supported above by b-c. These are the
  correct reversal directions for the two equivalences.
- The ring, one-object site, coefficient modules and chosen small derived Hom
  universe all have the existing common size u used by the consuming parent.
  u is explicit and arbitrary. There is no test-algebra universe assumption.

Searches for reuse (all via the prescribed wrapper, with results also retained
by msearch):

- LeanFinder: "A complete Noetherian local ring admits a dualizing complex giving
  canonical biduality on all unbounded complexes with finite cohomology".
  Eight hits: derived-category t-structure, representative and K-injective lemmas;
  no coherent duality existence theorem.
- LeanSearch: "Derived coherent duality complete Noetherian local ring dualizing
  complex". Eight hits on cotangent spaces, standard derived categories, ordinary
  linear duality and Picard groups; no match.
- Loogle: `DerivedCategory, CategoryTheory.Equivalence`: zero hits.
- Mathlib grep via msearch: `[Dd]ualizing|[Bb]iduality|derivedHom` in Algebra:
  one unrelated HomotopyFiber comment; no match.
- rg on upstream `WeilConjectures`, side `lean/Sheaf/Algebra` and `RingTheory`:
  derived/internal Hom, biduality and dualizing patterns. Found the shared
  one-object ring site, signed normalized calculus, and the semidualizing
  conservativity parent; reused them. Etale dualizing statements have different
  objects. No existing statement gives 0BFR(2)+0A7C for ordinary modules.
- Exact item-id rg on upstream `WeilConjectures`: zero hits.
- Exact proposed names rg on Mathlib, upstream, side sources and
  `dag/lean_names_upstream.json`: zero hits before this module was written.

Validation: scompile.py compiled this file as sandbox and as its final library
module, each clean (2.5 s and 3.0 s). No compiler warnings or errors were printed.
Every variable/universe is bound, with `set_option autoImplicit false`.

## Second reading by Q130

Author's separate reread of the node, its sources and the saved Lean module;
the dispatcher explicitly forbids starting another agent, and independent review
is the maintainer's. This section does not claim an independent worker review.

The reread checked every clause against the above list. The category predicate
quantifies over all integer degrees without bounds; the equivalence is from the
OPPOSITE full subcategory and its natural comparison is with the actual recorded
RHom functor. Ω alone is required to be bounded. Both boundedness reversals are
correct. The canonical map transposes evaluation with D(K) as right tensor
parameter, and the braiding is required to put the evaluation inputs in order.
The final equation uses the dual functor twice and has source K and target D(D(L)).
No extra injective-dimension assumption is imposed on K or on the ring. Definitions
have full data and the only theorem has proof `sorry`. No mismatch or change was
found in this reread.
