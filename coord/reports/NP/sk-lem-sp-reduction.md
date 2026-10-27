## Worker report

`Sheaf.SecSmoothPurity.Reduction` states `AlgebraicGeometry.ProEtale.sp_reduction`,
with one postponed proof. No definition is introduced or copied. The source is the
current blueprint unit `sec-smooth-purity/sk-lem-sp-reduction/_section.md`, read
together with the accepted DAG statement and its five proof steps.

Hypothesis and clause correspondence:

- The prime is `(ℓ : ℕ) [Fact ℓ.Prime]`. Positive characteristic distinct from ℓ is
  `(pchar : ℕ) (hp : 0 < pchar) (hℓ : pchar ≠ ℓ)`, with `(k : Type u) [Field k]
  [CharP k pchar]`. Field characteristic is automatically prime when positive.
- Schemes over this field are `X`, `Y`, `Z : Scheme.{u}` with their `Over` instances.
  For each structure morphism, `LocallyOfFiniteType`, `QuasiCompact` and
  `IsSeparated` express separated finite type. `f.IsOver` is k-linearity of f.
- Smooth pure relative dimension is `(d : ℕ) [SmoothOfRelativeDimension d f]`.
  This is Mathlib's recorded smooth-of-relative-dimension notion, including d=0.
- The coefficient-independent chosen compactification is displayed by `j`, `p`,
  their open/proper and k-morphism instances, and `hf : j ≫ p = f`. It is the
  same factorization on both sides. The theorem is valid for every such choice,
  so in particular for the setting's `compactificationOverField`. These are the
  supplied compactification data, not a compactifiability assumption on f.
- `{A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]` and
  `φ : A →+* B` give exactly a homomorphism of finite commutative rings. `hA`
  and `hB` give potentially different annihilating powers of ℓ. There is no
  flatness, finite projective dimension, nonzero-ring or nonzero-exponent binder.
- `spFiniteConstructibleTorCategory T R` is the already recorded full category
  of bounded complexes with intrinsic constructible cohomology and finite Tor
  amplitude. It uses `IsConstructibleProEtaleModuleSheaf` and
  `HasFiniteProEtaleTorAmplitude`, retained secondary declarations of the two
  recorded dependency interfaces. Thus fixed-module primary declarations are
  not incorrectly applied to ring-sheaf modules and no definition is duplicated.
- `scalarExtensionCtfFunctor ℓ hA hB φ T` is exactly the statement dependency's
  extension of coefficients on this category, on objects and on arrows.
- `hFA`, `hFB` certify the compact-support restrictions. The actual functors are
  the inline `ObjectProperty.lift` of the inclusion followed by
  `reductionCompactSupport`. This is definitionally the recorded restriction,
  and changes no object or morphism.
  `GA`, `GB`, `adjA`, `adjB` existentially supply the indicated restricted
  exceptional right adjoints and their adjunctions. This includes the stated
  existence convention rather than assuming arbitrary maps in their place.
- `hb` asserts invertibility of the specified `reductionDirectImageComparison`
  at every `M`. This is b(M), already a natural transformation, constructed by
  commuting coefficient extension past the open and proper factors. Both
  endpoints belong to the full target category by hFA/hFB and the scalar functor.
  `IsIso` in the ambient category therefore gives precisely the displayed Dctf
  isomorphism. It is not just an isomorphism of cohomology groups.
- `c` is a natural transformation `GA ⋙ (-)_B ⟶ (-)_B ⋙ GB`, so its components
  are natural in K. The final clause states `IsIso (c.app K)` for every K.
- The displayed equality uses Lean's left-to-right `≫`: its left side is
  `Rf_!,B(c_K)` followed by `ε_B(K_B)`; its right side is the inverse of the
  canonical b at `GA K`, followed by scalar extension of `ε_A(K)`. Hence its
  order is exactly the source counit identity. `∃! c` records uniqueness. The
  adjunction hom-equivalence also makes the counit equation alone determine
  every component uniquely; invertibility is an additional asserted property.

Dependency declarations read and reused:

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `CondensedRing.compactificationOverField`, the setting's compactification.
  Its `Compactification.overObj/overI/overG` definitions are in
  `WeilConjectures.Compactification.Over`. The present statement exposes the
  same data as j and p so the source's chosen compactification can be substituted.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`,
  `SmoothOfRelativeDimension`; read their class signatures and docstrings.
- `Sheaf.Paper.ProEtaleFixedModuleConstructible`: retained
  `Scheme.IsConstructibleProEtaleModuleSheaf` from
  `Sheaf.Paper.ProEtaleConstructibleSheaf`, used by the existing full category.
- `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitudePresentations`: retained
  `Scheme.HasFiniteProEtaleTorAmplitude` and `HasProEtaleTorAmplitude`, from
  `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude`.
- `Sheaf.Paper.SmoothPurityScalarExtension`: `scalarExtensionCtfFunctor` and
  its membership theorem, with no coefficient-flatness requirement.
- `Sheaf.Paper.FiniteLocalizingExceptionalPreservation`:
  `CondensedRing.localizingExceptionalAdjoint_preserves_finiteConstructible`,
  supplying restricted constructible adjunctions.
- `Sheaf.Paper.SmoothPurityNormalizedTowers`:
  `spFiniteConstructibleTor`, `spFiniteConstructibleTorCategory`.
- `Sheaf.SecSmoothPurity.ReductionDirectImageComparison`:
  `reductionCompactSupport`, `reductionDirectImageComparison`.
- `Sheaf.SecSmoothPurity.ReductionDirectImage`: `reductionDirectImage_isIso`.
- `Sheaf.SecSmoothPurity.ScalarExtensionFunctor`: `scalarExtensionFunctor`,
  used for the ambient image of the A-counit.
- `Sheaf.SecSmoothPurity.ReductionExceptional`: `reductionExceptional_isIso`,
  imported privately for the proof only. Its restriction helper definitions
  were read to check the inline lift and the recorded scalar restriction.
  Neither helper is used by the repaired signature.

The already published nodes `sk-def-sp-normalized-towers`,
`def-sp-reduction-direct-image-comparison`, and `det-sp-scalar-extension-functor`
were added to stmt_deps because their recorded declarations occur in the
signature. All original fields other than lean and this permitted addition to
stmt_deps are unchanged. No new node, dependency module, or statement correction.

Edge cases checked before writing: empty schemes and zero complexes are allowed;
there is no nonempty or nontrivial binder. The zero ring is allowed. The power
annihilating each ring may be zero (then that ring is zero); the powers need not
agree. Identity ring maps and nonflat quotient maps are included, including
quotients of rings such as Z/ℓ². d=0 is included. In the identity geometric case
the formula is the adjunction transpose of the coefficient-extended counit.
The site retains object universe u+1 and morphism universe u via the recorded
ring-sheaf derived category; there is no extra universe equality on the site.
All variables and the universe are explicitly bound; autoImplicit is false.

Searches (actual msearch results are also recorded in searches.jsonl):

- LeanFinder, `Derived coefficient extension commutes with compact support and
  exceptional pullback for smooth scheme morphisms`: eight hits, all scheme
  appLE/composition and immersion formulas; no coefficient comparison theorem.
- Loogle, `CategoryTheory.Adjunction.homEquiv`: twelve hits on adjunction
  hom-equivalences and naturality. This supplies generic formalism, not this
  geometric theorem.
- msearch grep, `reductionExceptional|reductionDirectImage|coefficientComparison`:
  zero Mathlib hits.
- LeanSearch, `Derived change of finite ring coefficients commutes with smooth
  exceptional pullback and compact support pushforward`: eight hits on smooth
  ring maps and their algebraic base change; no match.
- rg over Mathlib with the same comparison-name pattern: no hits. rg over
  `lean/WeilConjectures` and `lean/Sheaf` for `sp_reduction`,
  `reductionExceptional_isIso`, `reductionDirectImageComparison`, and the item id:
  no exact upstream combined statement. The detailed Sheaf comparison nodes
  were found, read, and reused. Upstream name-index search found unrelated
  algebraic reductions. The detailed exceptional theorem additionally asserts
  ordinary-site realizations and normalized chart equations, so it is not an
  exact existing declaration of this node's combined b/c statement.

Validation: scompile.py compiled both the sandbox module and its library-path
form cleanly. An initial private-import visibility error and an incorrectly
unwrapped full-subcategory argument to hb were repaired. The final form directly
uses scalarExtensionCtfFunctor. No mathematical statement fault was found.

## Repair of returned head 7cc8bcefd362

H2: Removed `det-sp-reduction-exceptional` from stmt_deps and retained it in
proof_deps. Inlined the two `ObjectProperty.lift` expressions formerly hidden
behind `reductionCtfCompactSupport`. These are its exact defining terms, so the
adjunctions and counits are unchanged definitionally. No helper definition or
new node is introduced. `ReductionExceptional` and `ReductionDirectImage` now
have plain proof imports; `ReductionDirectImageComparison` is publicly imported
for the actual definition interface. The sandbox was compared with the current
main node: the natural-language statement, proof, original statement dependencies
and proof dependencies are preserved. Only lean and the permitted additions to
stmt_deps differ. The supplied return identifies the immutable returned head;
the retained sandbox is the version being repaired.

Advisory: added `det-sp-scalar-extension-functor` to stmt_deps and publicly imported
its module, since the signature applies `scalarExtensionFunctor` to the A-counit.
Existential GA/GB and their adjunctions are retained. For any other right adjoints,
the unique counit-preserving right-adjoint isomorphisms transport the conclusion,
so existence here also supplies the source's indicated adjoints.

H11: replaced the former three-sentence second-reading section by the explicit
clause-by-clause reading below. This is the dispatcher's worker's rereading;
no independent worker was started or claimed. The maintainer independently
reviews the repaired immutable delivery.

## Second reading by NP

I reopened the complete DAG statement and the repaired Lean module and compared
them in order. The following reading addresses each hypothesis and clause.

1. Standing characteristic: the node requires a field of positive characteristic
   p distinct from the prime ell. The binders `ℓ pchar`, `Fact ℓ.Prime`, `hp`,
   `hℓ`, `Field k` and `CharP k pchar` state exactly these conditions. No
   algebraic-closure or perfection condition has been introduced.
2. Schemes and maps: X and Y each have `Over (Spec (.of k))` and locally finite
   type, quasi-compact, separated structure maps. These are separated finite-type
   k-schemes, and `f.IsOver` makes f a k-morphism. The same conditions on Z keep
   the compactification inside the setting, as required by the standing node.
3. Smoothness and dimension: `d : ℕ` and `SmoothOfRelativeDimension d f` state
   smooth pure relative dimension d. Zero is allowed; there is no positivity
   condition on d. Smoothness is included in this recorded notion.
4. Compactification: j is open, p proper, each over k, and `hf : j ≫ p = f`.
   The same j and p are used throughout both coefficient rings. The theorem
   applies to every supplied choice, hence to the setting's fixed choice.
   No comparison is replaced by an arbitrary natural isomorphism.
5. Rings: both A and B have `CommRing` and `Finite`, and `φ : A →+* B` is their
   ring map. The existential exponents in hA and hB are independent and permit
   exponent zero and the zero ring. Neither flatness nor finite projective
   dimension is assumed. Nonflat quotients remain included.
6. Categories and coefficients: every M and K ranges over the recorded
   `spFiniteConstructibleTorCategory` for its indicated scheme and coefficient
   ring. This is the full derived category restriction with bounded intrinsic
   constructible cohomology and finite Tor amplitude. The functor
   `scalarExtensionCtfFunctor ℓ hA hB φ T` is exactly the recorded (-)_B.
   The definitions retain the small pro-etale site with its original universes.
7. Compact-support and exceptional functors: hFA/hFB assert membership of the
   actual compact-support outputs. Each inline lift in adjA/adjB is inclusion
   followed by the existing ambient compact-support functor, with precisely
   that membership witness. This is the exact defining body of the former
   restriction helper. GA/GB and adjA/adjB supply the constructible adjunctions,
   including their actual counits; no arbitrary counit is passed separately.
8. First displayed isomorphism: hb quantifies over every M and asserts IsIso of
   `reductionDirectImageComparison φ j p` at M.obj. The comparison's definition
   is the proper counit mate composed with the normalized open scalar map.
   Its endpoints are respectively (Rf_!,A M)_B and Rf_!,B(M_B). The ambient
   transformation already supplies naturality in M. Since both endpoints are
   in the full subcategory, ambient invertibility is invertibility there.
9. Second displayed isomorphism: c has source GA followed by scalar extension
   on X and target scalar extension on Y followed by GB. Thus c.app K has
   exactly source (f_A^! K)_B and target f_B^!(K_B). Being a natural
   transformation supplies naturality in K; the final IsIso clause supplies
   the derived isomorphism, not only isomorphic cohomology sheaves.
10. Counit equation: the left side first applies the B compact-support functor
    to c.app K and then the B-counit at K_B. The right side first inverts the
    canonical b at GA K using hb, then applies ambient scalar extension to
    the A-counit. This is exactly the displayed equation in Lean's forward
    composition order. All terms use the same adjA/adjB and coefficient map.
11. Uniqueness: `∃! c` states uniqueness of the natural comparison satisfying
    the equation and invertibility. The equation alone determines each
    component by the bijective B-adjunction transpose, so this also renders
    the source's statement that c is uniquely determined by that equation.
    The proof plan explicitly invokes that bijection rather than inferring
    invertibility of mates from invertibility of b.
12. Edge cases and proof status: empty schemes, zero objects, zero rings,
    identity coefficient maps, arbitrary nonflat finite ring maps, and d=0
    are not excluded. The universe u is explicit and autoImplicit is false.
    There is exactly one theorem proof and it remains `sorry`.

The reading found the returned dependency-classification mismatch and the
missing direct citation for scalarExtensionFunctor, both repaired above.
There was no remaining mathematical mismatch with any source clause; the
statement itself and the proof dependency on the exceptional theorem are retained.
