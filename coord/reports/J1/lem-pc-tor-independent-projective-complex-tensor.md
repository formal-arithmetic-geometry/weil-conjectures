## Worker report

The item is stated in `lean/Sheaf/Algebra/Homology/TorIndependentProjectiveComplexTensor.lean`
as `ModuleCat.torIndependent_projectiveComplex_tensor`. The proof is `sorry`.
Its original statement, proof, and proof dependencies are unchanged. The only additions to
the item are its Lean record and the statement dependency for the new model definition.

Every hypothesis and clause is represented as follows:

- Commutative ring R and commutative R-algebras A, B: `{R : Type uR₁} {A : Type uA₁} {B : Type uB₁}`, the three
  `CommRing` instances, and `[Algebra R A] [Algebra R B]`.
- The usual first-variable projective-resolution Tor: `CategoryTheory.Tor' (ModuleCat R)`.
  This is exactly the recorded Mathlib declaration of `def-weil-pbc-tor-modules`.
  `hTor : ∀ i : ℕ, 0 < i → IsZero (...)` is vanishing for every positive degree;
  Tor in degree zero is not required to vanish.
- E is precisely `A ⊗[R] B`, with Mathlib's tensor-product commutative algebra structure.
  It is not an independently supplied ring with unspecified maps.
- Q is a cochain complex of A-modules: `Q : CochainComplex (ModuleCat A) ℤ`.
  Its differential and differential-square-zero equations belong to this Mathlib structure.
- Boundedness: `hbounded` says that all terms outside some integer interval [m,n]
  are zero objects. For integer degrees this is equivalent to finitely many nonzero terms.
- Finite projectivity: `hprojective` requires `Module.Finite A (Q.X i)` and
  `Module.Projective A (Q.X i)` in every degree. Over a commutative ring these say precisely
  that each term is a summand of a finite free A-module, as in the node's parenthesis.
- Localization D of E: `[CommRing D] [Algebra E D]` and
  `hlocalization : ∃ S : Submonoid E, IsLocalization S D`. The multiplicative subset is
  arbitrary, and the algebra map is the map at which D is a localization.
- Left-derived tensor, its E-action, and its canonical comparison use
  `ModuleCat.baseDerivedTensorCohomologyModel R A B Q D`, defined in the sibling module.
  This has an actual universal left-derived functor of R-to-B scalar extension, not an
  arbitrary cohomology type. Its `cohomologyIso i` identifies the underlying B-module of
  `cohomology i` with the actual derived-category cohomology of Q_R tensor^L_R B.
  Its `comparison_eq` identifies the ordinary comparison with the derived counit on
  cohomology, including the canonical tensor-associativity identification on generators.
- The source of `localizedComparison i` is `(extendScalars (algebraMap E D)).obj
  (cohomology i)`, namely D tensor_E H^i(Q tensor^L_R B). The node writes the factors
  in the opposite order; Mathlib's `TensorProduct.comm` gives the canonical symmetry.
- The target is the homology of termwise extension of Q along A -> E -> D, namely
  H^i(Q tensor_A D). The A-algebra structure on D is specified by this composite,
  rather than left unspecified.
- The canonical map is fixed by `localized_eq`: after restriction and precomposition
  with the scalar-extension unit, it is precisely the composite of `comparison i` and
  the cohomology of the termwise map e tensor q -> image(e) tensor q. The latter map is
  fixed by `ordinaryToLocalized_tmul`. Extension/restriction adjunction determines the
  D-linear map uniquely. Neither comparison map is assumed to be an isomorphism.
- The conclusion `∀ i : ℤ, IsIso (...localizedComparison i)` is that this very map
  is an isomorphism in every cohomological degree, rather than merely that some
  isomorphism between the two modules exists.

The `HasDerivedCategory.{w₁}` instances are choices of localization and morphism-size
universe, not flatness, Noetherianity, or mathematical existence assumptions. Mathlib
`HasDerivedCategory.standard` supplies the usual choice. All universes and variables
are explicitly bound. The module object universe is `max uR₁ uA₁ uB₁ uD₁ v₁`, with independent ring and module universes; there is no countability,
finite-rank bound, or small-ring restriction.

Dependency declarations used and read:

- `def-weil-pbc-tor-modules`: `CategoryTheory.Tor'`,
  `Mathlib.CategoryTheory.Monoidal.Tor`; its full definition derives tensoring in the first
  variable. `ModuleCat.Projective`, `ModuleCat.Abelian`, and `ModuleCat.Monoidal.Basic`
  provide its module-category instances.
- New model node: `ModuleCat.BaseDerivedTensorCohomologyModel`,
  `ModuleCat.baseDerivedTensorCohomologyModel`,
  `Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel`.
- The model uses the existing generic category and tensor notions, not copies:
  `DerivedCategory`, `DerivedCategory.Qh`, `DerivedCategory.homologyFunctor`, and
  `DerivedCategory.homologyFunctorFactorsh` in Mathlib's DerivedCategory Basic and
  HomologySequence modules (`def-weil-abstract-derived-category`);
  `TensorProduct` in Mathlib.LinearAlgebra.TensorProduct.Defs and
  `Algebra.TensorProduct`'s ring structure (`def-weil-pbc-module-tensor-product`);
  `LinearMap.baseChange` in Mathlib.LinearAlgebra.TensorProduct.Tower
  (`def-weil-module-base-change`), as packaged by `ModuleCat.extendScalars`.
  `Functor.IsLeftDerivedFunctor` is the existing localization/Kan-extension universal
  property, from Mathlib.CategoryTheory.Functor.Derived.LeftDerived.

Edge cases checked: zero rings and zero algebras are allowed; the zero complex is bounded
and termwise finite projective; an empty support is allowed by choosing m > n; the rank of
any term may be zero; the localization subset may contain zero, so D may be the zero ring;
no domain or nontriviality hypothesis is present; the tensor map for all these zero cases is
between zero modules. The interval may include negative degrees, and every i in Z occurs.
No characteristic restrictions or assumption that A or B is flat over R was inserted.

Searches for the existing statement and notions:

- msearch.py LeanFinder, `Tor independent bounded projective complex derived tensor base
  change`: eight hits, including `CategoryTheory.Tor'`, `Tor'_obj_obj`, and projective Tor
  vanishing; none is the bounded-complex localization comparison.
- msearch.py Loogle, `CategoryTheory.Tor\x27, CochainComplex`: zero hits and an unknown
  identifier error for the literal x27. This malformed early query is not relied on. A corrected Loogle query,
  `CategoryTheory.Tor', CochainComplex`, returned zero hits.
- msearch.py grep, `derived.*tensor|tensor.*derived`, Algebra/Homology: zero hits.
- msearch.py LeanSearch, `total left derived tensor cohomology module action base change
  comparison map`: service unavailable (Internal Server Error), recorded as unavailable.
- msearch.py LeanFinder, `derived tensor cohomology model with commuting scalar actions
  over tensor product algebra`: eight hits (cotangent base change and representation Tor),
  no such model or canonical map definition.
- msearch.py grep, `BaseDerivedTensorCohomologyModel|baseDerivedTensorCohomologyModel|
  derived.*tensor.*cohomology|extendScalars_additive`: zero hits.
- rg of the exact new names in WeilConjectures, lean/Sheaf, and dag/lean_names_upstream.json:
  no match. Searches of derivedTensor/leftDerived/tensor in WeilConjectures find the
  sheaf-derived tensor and generic total-derived-functor infrastructure, not this
  module tensor-algebra cohomology model or the item's comparison theorem.
- DAG search and `tools/blueprint_refs.py search 'derived tensor cohomology'`: no matching
  blueprint definition. The related `lem-pc-balanced-derived-tensor-model` and
  `lem-pc-derived-tensor-action-naturality` are statement nodes concerning resolution
  computations and actions, not existing Lean definitions of the present model. The
  generic abstract derived category, module tensor, and base change nodes are reused.
- The upstream item-id grep finds no existing item declaration.

The local literature checkout is absent. The source was read directly from the Stacks
project's raw `perfect.tex` on GitHub, at `lemma-compare-base-change` (Tag 08IB): the affine
proof explicitly identifies A tensor^L_R B with A tensor_R B under positive Tor vanishing.
The finite-projective complex statement is the item's stated local algebra consequence.
The new model's Tag 06Y6 source was also read on the Stacks website (More on Algebra),
`lemma-derived-base-change`: it constructs the universal derived scalar extension
using K-flat resolutions and localization.
No statement correction or dispute was needed.

Validation: both modules compiled together on the server, with no errors or warnings.
The only postponed proofs are the item's theorem and the model node's two supporting
proofs, each with its source and complete natural-language argument in its docstring.

## New nodes

`def-pc-base-derived-tensor-cohomology-model` supplies the missing reusable model of the
base-derived tensor's cohomology, tensor-algebra action, counit comparison, and canonical
localization map. Its source is Stacks Tags 06Y6 and 08IB. Its statement explicitly cites
`def-weil-abstract-derived-category`, `def-weil-pbc-module-tensor-product`, and
`def-weil-module-base-change`, using their Mathlib notions. The searches above found no
existing definition of this package. The sibling module defines the structure in full;
`nonempty_baseDerivedTensorCohomologyModel` supplies the existence proof, and the definition
`baseDerivedTensorCohomologyModel` selects actual structured data by classical choice.
No data is written as sorry: the deferred existence theorem has the construction of
all fields in its docstring. The separate named additive theorem (registered as an instance) supplies what
Mathlib's scalar-extension functor needs to act on the homotopy category. Both supporting
proof declarations belong to this definition node, with its blueprint tag.

## Earlier second reading (a previous round; superseded)

Pending: the dispatcher assigns an independent second reader after this worker's
READY response. This section records no completed independent reading.

## Repair of the previous attempt

Restored the full derived-functor model after rejecting a temporary simplification
that represented the comparison by identity endomorphisms of E. That simplification
was mathematically wrong and is absent from this delivery. The final module uses
actual derived cohomology and imposes no isomorphism assumption on either comparison.
The remaining universe error was fixed by supplying the first universe parameter
of `extendRestrictScalarsAdj`, which is the module universe, before the ring universes.
Tor is evaluated on universe lifts of R, A, B, allowing their universes to differ.
These lifts preserve tensor products and projective-resolution Tor canonically.
All supporting theorem proofs and the item proof are `sorry`; no result is proved.
The record signatures were refreshed from the restored files and all long Lean
lines were wrapped.


## Second reading by J1

I independently read the item node, both delivered modules, all four definition
nodes involved, and the signatures and bodies of their recorded Mathlib declarations.
No correction to the item's mathematical statement is needed. There are no dependency
replacement modules or statement-change citers to review.

Source check: I read `perfect.tex`, `lemma-compare-base-change` (Tag 08IB), including
its proof, from https://raw.githubusercontent.com/stacks/stacks-project/master/perfect.tex.
The proof reduces to affine schemes Spec(A), Spec(R), Spec(R'), and explicitly uses
positive Tor vanishing to identify the derived and ordinary algebra tensor products.
The global quasi-compact/quasi-separated assumption does not add a ring restriction
in this affine algebra consequence. I also read the preceding construction and proof
of `more-algebra.tex`, `lemma-derived-base-change` (Tag 06Y6), from
https://raw.githubusercontent.com/stacks/stacks-project/master/more-algebra.tex.
It constructs the left derived functor from K-flat resolutions for an arbitrary ring
map; specializing its second factor to B[0] gives the functor used here.
Neither source imposes a field, characteristic, Noetherianity, or flatness assumption
on the two algebras. The localization/cohomology clause follows by flat extension
from the ordinary E-complex, as the item's proof explicitly explains.

Here is the complete inventory of objects, hypotheses and conclusions, matched to
Lean. Each row passes.

| Node clause | Lean rendering and verdict |
| --- | --- |
| Commutative ring R | `{R : Type uR₁} [CommRing R]`; arbitrary commutative ring. |
| Commutative R-algebras A, B | Independent `Type uA₁`, `Type uB₁`, `CommRing` and `Algebra R` instances; no extra algebra conditions. |
| Usual projective-resolution Tor | `CategoryTheory.Tor'` derives tensoring in its first factor, as read in `Monoidal/Tor.lean:50`; the dependency records exactly this declaration. |
| Tor_i(A,B)=0 for every i>0 | `hTor : ∀ i : ℕ, 0 < i → IsZero (...)`; A and B, not their finite quotients, occur as the two objects. The ULifts place the ring and both modules in a common universe. Ring/module equivalence under ULift transports projective resolutions and tensor homology, so this is the same vanishing condition. |
| E=A tensor_R B | All E occurrences are the literal `A ⊗[R] B`, with Mathlib's commutative tensor-algebra ring and inclusion maps. E is not a separately chosen algebra. |
| A cochain complex Q | `Q : CochainComplex (ModuleCat A) ℤ` with the displayed larger module universe; includes its actual differentials and square-zero laws. |
| Bounded complex | `hbounded : ∃ m n : ℤ, ∀ i, i < m ∨ n < i → IsZero (Q.X i)`; bounded terms, not just bounded cohomology. |
| Every term finite projective over A | `hprojective : ∀ i, Module.Finite A (Q.X i) ∧ Module.Projective A (Q.X i)`; finite generation plus projectivity is precisely being a summand of some finite free A-module. The finite rank may vary with i. |
| D a localization of E | `(D : Type uD₁) [CommRing D] [Algebra E D]`, `hlocalization : ∃ S : Submonoid E, IsLocalization S D`; arbitrary multiplicative subset, with no nonzero or domain restriction. |
| Q tensor-derived-over-R B | The chosen model's `derived`, `counit`, `universal` fields use the actual Mathlib localization and `Functor.IsLeftDerivedFunctor`, read as the right-Kan-extension universal property of the counit. Q is first restricted along R to A. |
| Derived cohomology as E-module | `cohomology i : ModuleCat E`, with `cohomologyIso i` identifying its B-restriction with actual derived-category cohomology. `comparison_eq` fixes its comparison to ordinary E-cohomology as the derived counit under this identification. |
| Ordinary complex Q tensor_A D | Termwise `extendScalars` along `(algebraMap E D).comp (algebraMap A E)`; the A-action on D is exactly the prescribed composite. |
| Source H^i(derived tensor) tensor_E D | `(extendScalars (algebraMap E D)).obj (cohomology i)`; its carrier is D tensor_E H^i. Tensor symmetry identifies this with the node's factor order, preserving the D-action. |
| Target H^i(ordinary tensor) | `.homology i` of that D-module cochain complex; Mathlib homology of shape `.up ℤ` is cohomology. |
| The canonical map | `localizedComparison i` is constrained by `localized_eq`: after restriction and the adjunction unit it is `comparison i` followed by the cohomology of `ordinaryToLocalized`. The latter is fixed on all tensor generators by `ordinaryToLocalized_tmul`. Adjunction determines the D-linear map uniquely. |
| Isomorphism in every degree | `∀ i : ℤ, IsIso (...localizedComparison i)`; the canonical map itself is invertible, not merely an unspecified isomorphism between the objects. Negative, zero, and positive cohomological degrees all occur. |

I checked the potential action ambiguity carefully: `cohomologyIso` alone only
specifies the B-action. Here `comparison` is E-linear and its B-restriction is the
fixed counit comparison. Under this item's Tor and boundedness hypotheses that
comparison is an isomorphism on cohomology. It therefore forces the E-action on
`cohomology i` to be the canonical transported action, and forces the localized
map to be the source's map. No extra E-action hypothesis or conclusion is smuggled
into the theorem. Neither comparison's invertibility is a field of the model.

Dependency signatures checked: `TensorProduct` is the usual bilinearity quotient;
`LinearMap.baseChange` maps A tensor_R M to A tensor_R N and is packaged by
`ModuleCat.extendScalars`; `DerivedCategory`, `Qh`, `homologyFunctor`, and the two
cohomology factorization isomorphisms are the actual localization/cohomology
constructions. `HasDerivedCategory.{w₁}` selects the localization and its morphism
universe. `HasDerivedCategory.standard` supplies a common choice for both module
categories, so these binders impose no mathematical existence or finiteness
restriction. Ring universes are independent; the module universe is their maximum
with an independent v₁. Every ring and complex can be placed in such a universe.

Edge cases: zero rings/algebras, a zero term, rank zero and the zero complex are
allowed. Empty support is allowed (choose any interval, or m>n). Both a single
term in degree zero and complexes in arbitrary negative degrees are covered.
Degree-zero Tor is unconstrained. The multiplicative subset can contain zero,
allowing the zero localization; there is no `Nontrivial` assumption. There is no
index-family or scheme binder, so empty index sets are not applicable, and the
empty affine scheme is already represented by the zero ring. All characteristics
are covered. Added `set_option autoImplicit false` in both modules verifies that
no variable is silently introduced.

Independent searches (recorded by msearch.py for this item):

- LeanFinder: `bounded finite projective complex Tor independent localization
  cohomology tensor`; generic Tor and tensor results, no theorem with these clauses.
- Loogle: `"extendScalars" "Additive"`; malformed query (Function expected at String),
  not used as evidence of absence. The following valid named query was used instead.
- Loogle: `CategoryTheory.Adjunction.left_adjoint_additive`; exact existing
  adjunction theorem found and its signature read.
- LeanFinder: `extension of scalars functor additive left adjoint`; found
  `ModuleCat.extendRestrictScalarsAdj`, whose definition and universe parameters
  I read, along with `Adjunction.left_adjoint_additive`.
- Grep: `derivedTensor|tensorCohomology|IsLeftDerivedFunctor`; found the generic
  derived-functor predicates, not this tensor/localization theorem.
- LeanSearch: `cohomology derived extension scalars localization bounded projective
  complexes`; service unavailable (Internal Server Error), not a negative verdict.
- Independent rg of Mathlib, WeilConjectures and lean/Sheaf with `derived.*tensor`,
  `tensor.*derived`, `Tor.*[Ii]ndepend`, and searches for the exact delivered names:
  no existing exact statement or existing full model package. Generic sheaf tensor
  and module K-flat constructions were read as related, different declarations.
- DAG and project search found the landed `def-pc-ring-tensor-cohomology` and
  `RingTensorCohomology` module. I opened its entire module: its source and target
  carry only the second-factor B-action, and its baseChangeMap localizes B to C.
  It has no E-module cohomology or localization E to D of this item's source, and
  its target is an A-derived tensor rather than the ordinary Q tensor_A D.
  It cannot replace this model's declaration. The existing K-flat/Tor-acyclic
  comparison theorem also concludes an R-linear quasi-isomorphism of resolution
  tensors and supplies no E-linear localization map. These are not duplicate
  definitions of the model package supplied in this delivery.

New-node review (H12): `def-pc-base-derived-tensor-cohomology-model` introduces R,
A, B, Q, D itself and states exactly the package implemented by the structure:
`derived/counit/universal`, `ordinaryIso/ordinaryIso_tmul`,
`cohomology/cohomologyIso`, `comparison/comparison_eq`,
`ordinaryToLocalized/ordinaryToLocalized_tmul`, and
`localizedComparison/localized_eq`. Its three cited definition dependencies match
its `stmt_deps`. Its source construction is supported by 06Y6 and the affine
comparison of 08IB. Its id, chapter, unit, created.item/group, ancestor/via,
empty proofs, null match and three search kinds meet §5; no maintainer fields
were added. It is reusable for arbitrary Q and arbitrary E-algebra D, with no
Tor, boundedness, finite-projectivity or isomorphism condition hidden in it.
The structure is actual data, and the selecting definition uses choice from a
separately named existence theorem with a full construction docstring.

Mismatches and changes: no mathematical mismatch was found in the item or the
new definition node. I added `set_option autoImplicit false` in both modules to
make the explicit-binder check enforceable. I investigated replacing the helper
`extendScalars_additive` by the existing adjunction additivity theorem. That
adjunction changes the source module universe to `max uT v`, while this helper
is stated for an arbitrary input module universe v. Attempts to specialize it
also left unsolved universe constraints in automatic preservation instances.
Thus the helper's exact signature is not the existing theorem's signature;
I retained the original general helper and its complete natural-language proof.
No alternate version or instance remains. All three postponed proofs (helper,
model existence, item theorem) remain `sorry`; nothing was proved here.

Both module docstrings and every remaining declaration docstring give their
source and their own blueprint id. The item docstring carries all three proof
steps and all four proof dependencies. All lines are at most 100 characters.
The main signatures were checked against the JSON records; neither changed.
The final paired server compile passed with exit code 0 and no warnings.
The deliver2 dry run printed OK: the delivery passes preflight and compiles.
The node signatures also pass stage2_delivery.check_lean_text unchanged.
