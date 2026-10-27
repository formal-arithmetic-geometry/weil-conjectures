## Worker report

The delivery states `AlgebraicGeometry.Scheme.Modules.coherent_support_cycle_exact_sequence`
in `Sheaf.AlgebraicGeometry.CoherentSupportCycleExactSequence`. Its only theorem has
`by sorry`; all definitions in the companion module have actual data. No node statement
is corrected and no dependency record is changed.

Clause-by-clause correspondence:

- Field F: `(F : Type u) [Field F]`.
- Noetherian scheme X: `(X : Scheme.{u}) [IsNoetherian X]`. Mathlib's IsNoetherian
  extends exactly IsLocallyNoetherian X and CompactSpace X, the node's two conditions.
- Finite type over F: the structure morphism `(f : X ⟶ Spec (CommRingCat.of F))`
  with `[LocallyOfFiniteType f] [QuasiCompact f]`. This is a scheme over F without
  requiring a separate chosen Over instance or adding separatedness.
- Nonnegative k: `(k : ℕ)`; support-category indices are integers. In particular the
  preceding term uses `((k : ℤ) - 1)`, not truncated natural subtraction.
- Coherent modules: the landed `Scheme.Modules.CoherentObject X`, whose predicate is
  exactly `RingedSpace.IsCoherent X.toRingedSpace M`. This is finite type plus the
  finite-type-kernel condition, not merely finite presentation or quasi-coherence.
- C_r(X): `SupportCoherentObject X r`, the subtype using `HasSupportBound r M`.
  For r nonnegative this uses `topologicalKrullDim` of the nonzero-stalk subspace;
  for r negative it uses `Limits.IsZero M.val`. Thus C_(-1) has precisely zero
  objects (all isomorphic copies of zero, as appropriate for the isomorphism-class
  presentation), not all objects supported in dimension zero.
- Its inherited short exact sequences: `supportK0Relations` quantifies over actual
  module-sheaf morphisms f and g and a proof of f ≫ g = 0, and requires
  `(ShortComplex.mk f g h).ShortExact`. All three objects belong to C_r.
- K_0 presentation: `SupportK0` is the quotient of FreeAbelianGroup on those objects
  by the generated isomorphism and `[B]-[A]-[C]` relations. The explicit isomorphism
  relations are exactly the alternative presentation by isomorphism classes.
  `supportK0Class` is the actual quotient generator.
- Integral closed V of dimension k: `IntegralCycleIndex X k` consists of
  `IrreducibleCloseds X` of topological Krull dimension k. These index *integral
  closed subschemes*, rather than arbitrary closed immersions with duplicate
  representatives: give each support the unique reduced induced structure of
  `Scheme.IdealSheafData.reduced_induced_closed_subscheme` (01J3/01J4). Every
  integral closed subscheme has exactly one such support. Reducedness is not a
  discarded condition: it is the canonical scheme structure on each index.
- Z_k(X): `IntegralCycles X k = IntegralCycleIndex X k →₀ ℤ`, exactly finite
  formal integral sums. No locally finite infinite cycles are introduced on this
  quasi-compact scheme.
- Generic point eta_V: `cycleGenericPoint V = V.val.isIrreducible.genericPoint`.
  Mathlib's scheme QuasiSober instance provides existence; T0 gives uniqueness.
- The ambient local-ring module length: `cycleStalkLength M V` uses
  `Module.length (X.presheaf.stalk (cycleGenericPoint V))` of
  `(RingedSpace.moduleStalkFunctor X.toRingedSpace (cycleGenericPoint V)).obj M`.
  Thus the coefficient is length over O_X,eta, not over the residue field or O_V.
- Finite length: the theorem's first universal clause is
  `cycleStalkLength M.val.val V ≠ ⊤` for every V.
- Only finitely many nonzero stalks: the next clause asserts finiteness of exactly
  `{V | ¬ Subsingleton (M.val.val.presheaf.stalk (cycleGenericPoint V))}`.
- The homomorphism defined by inclusion: the existential `ι` is an additive
  homomorphism from SupportK0(k-1) to SupportK0(k), and
  `IsSupportK0Inclusion` fixes its value on every generator, including every
  isomorphic representative in the larger category. This uniquely determines it;
  no arbitrary unconstrained map is substituted for inclusion.
- The generic-length homomorphism: the existential additive homomorphism `c`
  satisfies `IsGenericLengthCycleMap`: evaluation of its value on every object
  class, at every V, equals the integer cast of `(cycleStalkLength M V).toNat`.
  The separate finite-length clause ensures this is the actual length; it does
  not silently map infinite length to zero. Coefficient equality in Finsupp is
  precisely the displayed finite-sum formula.
- Exactness at Z_k and the terminal zero: `Function.Surjective c`.
- Exactness at K_0(C_k), including the final kernel/image assertion:
  `c.ker = ι.range`. It implies c ∘ ι = 0 as part of the same exactness condition.
  No injectivity of ι is asserted.

Dependency declarations read and used:

- Mathlib.Algebra.Field.Defs: `Field`.
- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- Mathlib.AlgebraicGeometry.Noetherian: `IsLocallyNoetherian`, `IsNoetherian`;
  Mathlib.Topology.Defs.Filter: `CompactSpace`.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType: `LocallyOfFiniteType`;
  Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact: `QuasiCompact`.
- Mathlib.Topology.KrullDimension: `topologicalKrullDim`.
- Sheaf.AlgebraicGeometry.CoherentFiniteType: the public coherence predicate
  `RingedSpace.IsCoherent`, defined in WeilConjectures.AlgebraicGeometry.Coherent.
- Sheaf.CategoryTheory.RingedSiteModules: `ringedSiteModules`, transparently the
  existing Mathlib `SheafOfModules`; X.Modules is its scheme specialization.
- WeilConjectures.Topology.PresheafModuleStalkFunctor:
  `PresheafOfModules.moduleStalkFunctor`; on sheaves its carrier is the same
  existing stalk. Scheme module stalks follow the record's explicit convention:
  `RingedSpace.moduleStalkFunctor` from
  WeilConjectures.Algebra.Homology.ModuleStalkFunctor.
- Mathlib.RingTheory.Length: `Module.length`, `Module.length_ne_top_iff`,
  `Module.length_eq_add_of_exact` (the last is a proof dependency).
- Sheaf.AlgebraicGeometry.CoherentGrothendieckSupport: `CoherentObject` is reused.
  Its `CoherentG0` is unrestricted; `coherentG0Filtration` is an image subgroup,
  so neither is K_0 of the bounded support category.
- Mathlib.Algebra.Homology.ExactSequence and ShortComplex.ShortExact:
  inherited short exactness in the abelian module-sheaf category.
- Mathlib.Topology.Irreducible and Sets.Closeds: `IsIrreducible`,
  `IrreducibleCloseds`; Mathlib.Topology.Sober: `IsIrreducible.genericPoint`.
- Proof imports, with full signatures/docstrings read: the recorded upstream
  `closedImmersion_coherent_equivalence`, `closedImmersion_pushforward_stalks`,
  `exists_coherent_filtration_integral_subschemes`, `coherent_kernel_cokernel_sum`,
  `finite_type_module_support_closed`, `integral_ideal_generic_stalk`,
  `module_stalk_exact`, `Scheme.IdealSheafData.reduced_induced_closed_subscheme`,
  and `isCoherent_iff_isQuasicoherent_and_isFiniteType`, in the identically named
  recorded modules listed in the theorem's imports. The seven-step proof
  docstring follows the accepted node proof, not a new route.

Edge cases checked before writing: k=0 gives the zero-object category on the left;
r=-1 does not accidentally include skyscraper sheaves; the zero module has empty
support and zero generic lengths; empty X has no irreducible closed indices;
k larger than dim X gives an empty cycle basis; all characteristics are allowed;
no hypothesis of reducedness, integrality, nonemptiness or separatedness on X was
introduced. Nonreduced X is allowed and multiplicity uses the ambient local ring.
All universes and variables are explicit. Enlarging u accommodates the field and
scheme in the usual scheme size convention; no unrelated test-object universe
makes a hypothesis vacuous. There are no local notations/instances or hidden lets.

Searches actually run through msearch.py (full results are in the new node):

- LeanFinder: “The Grothendieck group of coherent sheaves filtered by support
  dimension has a surjective generic length cycle map whose kernel is the image
  of smaller support”. Eight hits: general Grothendieck categories and affine
  module support, no matching theorem or cycle presentation.
- Loogle: `FreeAbelianGroup, AddSubgroup.closure, Module.length`: zero hits.
- LeanSearch: “Grothendieck group of coherent module sheaves with support
  dimension bound, free abelian group of integral closed subschemes of dimension k”.
  Eight hits, all monoid Grothendieck completion, no exact-category presentation.
- Mathlib grep: `Grothendieck|genericLength|supportFiltration` in AlgebraicGeometry
  found general Grothendieck topology uses; the narrower
  `SupportK0|supportK0|CycleGroup|genericLength|coherentG0` gave zero hits.
- Project rg over WeilConjectures and Sheaf found no SupportK0/genericLength/cycle
  interface. The literal item-id search in WeilConjectures gave no declaration.
  Broader concept search found CoherentGrothendieckSupport, which is reused, and
  CoherentGroupPresentation, whose ordinary group is unrestricted. No definitions
  of their existing notions are copied.
- DAG definition search for Grothendieck groups/free abelian integral cycles found
  the existing unrestricted coherent groups, finite-projective K0 and divisor
  groups on curves. None supplies C_r(X)'s group or general k-cycles. The blueprint
  searches `coherent support` and `cycle group` gave zero matches;
  `blueprint_refs.py ancestor` returned None.

Sources opened: chow.tex labels lemma-Serre-subcategories, lemma-cycles-k-group,
lemma-length-finite, definition-cycle-associated-to-coherent-sheaf, and the current
blueprint direct-images proof under literature/blueprint/latest. The assigned node
is the finite-type-field, Krull-dimension specialization of those Stacks statements.
No STATEMENT-DISPUTED flag or source correction is needed.

Validation: scompile.py compiled both delivered modules individually in dependency
order against the live published build, with no errors or non-sorry warnings.

## New nodes

`def-sfb-coherent-support-cycle-data` introduces the missing bounded category and
its actual K0 presentation, dimensional integral cycle indices and free group,
generic point and local length, and the two generator characterizations. Source:
Stacks 02S8/02S9/02QW/02QX and 02MX. Its searches are the actual logged searches
above. The existing CoherentObject is reused. The existing G0 filtration is an
image subgroup of G0, and therefore cannot replace K0(C_r); the cycle basis is
not the special divisor basis on a smooth curve. Finsupp is Mathlib's existing
free abelian group encoding, not a new algebraic structure. No theorem or axiom
is introduced in the definition module. Reduced induced structure is indexed by
its unique closed support, so no arbitrary closed-immersion choices enter cycles.

## Second reading by Q11

The dispatcher explicitly prohibits starting other agents; this section records
my separate second pass, not an independent worker's review. The maintainer's
independent review remains the delivery review specified by the prompt.

I reopened the node and the two modules and checked each correspondence above.
The important distinctions are K0(C_r) versus the image in unrestricted G0,
integer k-1 at k=0, length over the ambient local ring, and a basis with only one
representative for each reduced integral closed subscheme. All are retained.
The inclusion map is pinned on every object class and the cycle map on every
coefficient of every object class, hence their existential formulation is a
statement of existence of the specified canonical maps, not a hypothesis of an
arbitrary map. The finite-length and finite-support claims occur before these
existentials and are not assumed. I added the reduced-induced and exact-sequence
public dependency imports to the definitions module on this pass. I found no
mismatch requiring a mathematical statement change. Neither the new definition
node nor the theorem adds a proof beyond the single expected sorry.
