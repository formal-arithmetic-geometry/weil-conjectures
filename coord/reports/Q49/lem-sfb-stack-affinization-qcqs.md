## Worker report

The module `Sheaf.AlgebraicGeometry.StackAffinizationQcqs` states
`CategoryTheory.stack_affinization_qcqs`. Its helpers construct the actual pullback
of functions from an affine target: `moduliAffineGlobalPullbackFamily` evaluates
the Yoneda scheme map on each object, its named compatibility theorem supplies
the section condition, and `moduliAffineGlobalPullback` is the resulting ring
homomorphism into the existing compatible-family section ring. Both theorems
have `sorry` proofs and complete source/proof docstrings. Definition data are
explicit, including pointwise ring-homomorphism laws; no object is chosen from a
mere existence assertion.

Hypothesis and conclusion correspondence, with the node and source open:

- A field k: `(k : Type u) [Field k]`.
- An algebraic stack over k: `(F : BasedCategory.{v, w} (Over (Spec (.of k))))`
  and `hF : IsAlgebraicModuliStack F`.
- Its structural map is quasi-compact: `hqc` applies the recorded
  `IsQuasiCompactAlgebraicModuliMap` to the recorded `moduliBaseStructure F`.
- Its structural map is quasi-separated: `hqs` applies the recorded
  `IsQuasiSeparatedAlgebraicModuliMap` to the same structural map.
- R is exactly Gamma(F,O): the codomain of `e` is
  `moduliGlobalSectionsRing (moduliStructureSheaf F hF.1.1)`, the dependency's
  actual compatible-family ring, with pointwise operations.
- Spec R: the conclusion supplies `B : CommRingCat.{u}` and a ring equivalence
  `e : B ≃+* R`. Thus Spec B represents Spec R in the scheme universe. This is
  a conclusion, not a smallness hypothesis. Quasi-compact smooth atlas descent
  identifies the global functions with a subring/equalizer of small section rings.
  This is the same representation already used by the landed consumer
  `adequate_product_affinization`. No equality of independent universes is imposed.
- Existence of a k-morphism: `q : Spec B ⟶ Spec (.of k)` and a `BasedFunctor`
  from F to `discreteModuli (yoneda.obj (Over.mk q))`. Being based enforces the
  k-structure on every scheme object. Together with evaluation, it also fixes q
  to the canonical structural pullback of k.
- Restriction on every scheme morphism V → F: for every `x : F.obj` and `b : B`,
  `moduliAffineGlobalPullbackFamily a b x = ((e b).1 (op x)).down`.
  Objects over V are its scheme tests in the fibred-groupoid convention. The
  left side is `(Scheme.ΓSpecIso B).inv` followed by pullback of the actual
  Yoneda scheme map, exactly the affine-target correspondence of Tag 01I1.
- Quasi-compactness and quasi-separatedness of a: the next two conjuncts use
  the dependency predicates without replacement or additional representability.
- Identity on global functions: `moduliAffineGlobalPullback hF.1.1 a = e.toRingHom`.
  Transporting by e makes this precisely id_R; the pullback is an explicit ring
  map into compatible families, not an unconstrained extra map.
- Uniqueness up to 2-isomorphism: every other based map `a'` with the prescribed
  restrictions satisfies `Nonempty (ModuliTwoIso a' a)`. This is uniqueness of
  the characterized map, without assuming qcqs or identity separately for a'.
- The closing no-extra-hypotheses clause is respected: there is no finite-type,
  separated-diagonal, representable-morphism, or moduli-space assumption.

Universes: `u` is the scheme/ring universe, while F's morphism and object
universes `v,w` are independent. The qc map predicate's auxiliary test universes
`t,s` are explicit and identical in the input and conclusion; the predicate itself
uses maxima including both endpoints and the scheme site. The larger global-section
ring is used as recorded, with only the existing canonical ULift transport on its
values. The small presentation B is existentially supplied, not assumed.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`, `Field` (via imports).
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`, `IsAlgebraicModuliStack`.
- `Sheaf.AlgebraicGeometry.StackQcqsMorphism`,
  `IsQuasiCompactAlgebraicModuliMap`, `IsQuasiSeparatedAlgebraicModuliMap`.
- `Sheaf.AlgebraicGeometry.StackQuasiCoherentAlgebra`, `moduliSchemeForget`,
  `moduliStructurePresheaf`, `moduliStructureSheaf`, `moduliGlobalSectionsRing`.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids` (transitive public import),
  `BasedCategory`, `IsFibredInGroupoids`, `discreteModuli`, `ModuliTwoIso`.
- `Mathlib.AlgebraicGeometry.Scheme`, `Spec`, `Spec.map`, `Scheme.ΓSpecIso`.
- `Mathlib.AlgebraicGeometry.GammaSpecAdjunction`, `ΓSpec.adjunction`: the recorded
  affine-target bijection. The signature uses its explicit pullback direction
  `(Scheme.ΓSpecIso B).inv ≫ Scheme.Γ.map f.op`, as in `ext_to_Spec` and
  `ΓSpecIso_inv_ΓSpec_adjunction_homEquiv`.
- Added existing landed statement dependency `def-sfb-relative-moduli-inertia`:
  `Sheaf.AlgebraicGeometry.RelativeModuliInertia`, `moduliBaseStructure`. This
  is the structural-map convention, not a new definition or dependency repair.

The proof dependency `lem-sfb-algebraic-stack-fibre-products` is stated and is
privately imported through `Sheaf.AlgebraicGeometry.AlgebraicStackFibreProducts`.
The scheme proof facts are supplied by the private Mathlib QuasiSeparated import
(including affine quasi-separatedness and qcqs cancellation/base change).
`lem-sfb-representable-stack-quasicompact-tests` and
`lem-sfb-stack-quasiseparated-cancellation` have no recorded Lean declarations,
so there are no modules to import for those proof-only prerequisites. They are
not needed to type the statement; their proof steps remain in the docstring.
No statement dependency is missing or replaced by a private copy.

Edge cases checked before writing: the empty stack has zero global ring, with
empty spectrum and its unique map; no nontriviality of B is assumed. For an affine
scheme the characterization recovers its identity affinization. A proper connected
scheme with global ring k maps to Spec k. For BG the map need not be representable;
no such assumption was inserted. Arbitrarily large fibred-category universes and
all qcqs test universes remain independent. The isomorphism e retains every
function and every object evaluation, including the zero-ring case.

Source reading: Stacks `stacks-morphisms.tex`,
`lemma-quasi-compact-quasi-separated-permanence` (075S), clauses (1)--(3) and proof;
`schemes.tex`, `lemma-morphism-into-affine` (01I1), statement and construction;
`stacks-sheaves.tex`, `definition-structure-sheaf` (06TV) and the following
functoriality discussion. The node's six proof steps are preserved and expanded
in the theorem docstring. No node fault or disputed statement was found.

Searches actually run (logged by msearch.py):

- LeanFinder: “A quasi compact quasi separated algebraic stack has a canonical
  quasi compact quasi separated map to the spectrum of its global functions”.
  Eight scheme hits, including the qc and qs instances for `Scheme.toSpecΓ`;
  no stack statement.
- Loogle: `AlgebraicGeometry.Scheme.toSpecΓ, AlgebraicGeometry.ΓSpec.adjunction`.
  One hit, `ΓSpec.adjunction_unit_app`; scheme-only.
- Mathlib grep: `affinization|Affinization|toSpecΓ` in AlgebraicGeometry.
  Twenty-five hits, all schemes; no existing stack theorem.
- LeanSearch: “An algebraic stack has a canonical morphism to the spectrum of
  global sections of its structure sheaf”. Eight hits for the ring/scheme/locally
  ringed-space spectrum constructions, no fibred-groupoid theorem.
- `rg` in `lean/WeilConjectures` for `affinization|Affinization`, and the node id:
  derived scheme-affinization comparison only, no declaration for this node.
- `rg` in `lean/Sheaf` for stack affinization and `moduliGlobalSections`:
  existing consumers `AdequateProductAffinization`, `AdequateRelativeSpectrum`,
  `AdequateBaseChangeAffinization`, but none states this general qcqs result.
  Their helper `moduliRepresentableSchemeMap` is not copied; the current helper
  constructs the different ring pullback family directly. Importing that consumer
  would close its eventual proof-import cycle, so it is not imported here.
- `rg` in `dag/lean_names_upstream.json`, Mathlib, WeilConjectures and Sheaf
  for the new declaration names: no existing definitions of these pullback families
  or the general theorem.

Validation: scompile.py compiled the final module in both sandbox and library
module modes with no errors or non-sorry warnings. Every compiler probe started
with `module`; diagnostic commands were removed. Only the authorized wrappers
write compilation/delivery bookkeeping. No shared file was edited.

## Second reading by Q49

Worker self-check; the dispatcher brief forbids starting another agent, and the
maintainer supplies the independent review. Reopened the JSON statement and
finished Lean file and checked each clause against the correspondence above.
The quantified objectwise evaluation is the restriction to every scheme test,
not just an atlas; the ring identity is stated for the actual constructed
pullback. Uniqueness assumes only the restriction characterization. The qcqs
hypotheses and conclusions use identical auxiliary test universes and the
recorded predicates. The target presentation e is in the conclusion, so it
adds no restriction, and the based map enforces the k-structure. No clause was
dropped or strengthened; no statement correction, new node or dependency repair
was necessary. The only stmt_deps addition is the already landed owner of the
structural map, whose full definition was read before use.
