## Worker report

The module `Sheaf.AlgebraicGeometry.UniversalThickeningAffineCase` states
`AlgebraicGeometry.isUniversalFirstOrderThickening_spec`, with proof `sorry`.
No definitions, new nodes, dependency modules, or statement corrections are needed.

Hypothesis and conclusion correspondence:
- Commutative rings R, S, S': `(R S S' : Type u)` and their three `CommRing` instances.
- The ring homomorphism φ : R → S is `algebraMap R S`, supplied by `[Algebra R S]`.
  Every ring homomorphism gives this algebra structure, so this encoding imposes no
  extra mathematical hypothesis. `[Algebra R S']` supplies R → S'.
- The R-algebra map π is `(π : S' →ₐ[R] S)`; its algebra-map compatibility supplies
  π ∘ (R → S') = φ, without a separate assumption.
- Surjectivity is `hπ : Function.Surjective π`.
- K² = 0 is `hK : RingHom.ker π.toRingHom ^ 2 = ⊥`.
- Every R-algebra A, every square-zero ideal I, and every a : S → A/I appear in
  `hUniversal`, with no finite generation or nonzero-ring restrictions.
- The quotient map q is `Ideal.Quotient.mkₐ R I`. Existence and uniqueness of a'
  with q ∘ a' = a ∘ π is the `∃!` clause using `AlgHom.comp`.
- X, Z, Z' are the spectra of `CommRingCat.of R`, `CommRingCat.of S`, and
  `CommRingCat.of S'`, implicit in the domain and codomain of the three `Spec.map` terms.
- h, i, h' are respectively Spec of `algebraMap R S`, `π.toRingHom`, and
  `algebraMap R S'`, in that order in `IsUniversalFirstOrderThickening`.
- Closed immersion and square-zero defining ideal sheaf are precisely the first
  conjunct `IsFirstOrderThickening i` of that recorded predicate, whose definition is
  `IsClosedImmersion i ∧ i.ker ^ 2 = ⊥`.
- h' ∘ i = h is its second conjunct `i ≫ h' = h`.
- The full universal property is its last conjunct, quantifying over arbitrary
  `T T' : Scheme.{u}`, `j : T ⟶ T'`, `b : T' ⟶ X`, and `a : T ⟶ Z`, requiring
  `IsFirstOrderThickening j` and `j ≫ b = a ≫ h`, and concluding
  `∃! a', a' ≫ h' = b ∧ j ≫ a' = a ≫ i`. There is no affineness assumption.

Dependency declarations read and used:
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` and `Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`: `Scheme.Hom.ker`, ideal-sheaf power
  instance, and `Scheme.IdealSheafData.ideal_pow`, through `IsFirstOrderThickening`.
- `Sheaf.AlgebraicGeometry.Thickening`: `AlgebraicGeometry.IsFirstOrderThickening`.
- `Sheaf.AlgebraicGeometry.UniversalFirstOrderThickening`:
  `AlgebraicGeometry.IsUniversalFirstOrderThickening`, imported and used directly.
- `Mathlib.RingTheory.Ideal.Quotient.Operations`: `Ideal.Quotient.mkₐ`.

Edge cases: zero rings and empty spectra are permitted; I = ⊥ and the zero ring
quotient are permitted. No characteristic or finiteness is imposed. Test schemes
may be empty or non-affine. Rings, test algebras, and test schemes share an arbitrary
universe u, so the lifting hypothesis covers the global-section rings of the test
schemes and cannot become vacuous by choosing a smaller independent test universe.
The theorem assumes the ring universal property itself, so no formal-unramifiedness
hypothesis is needed in addition. The six proof steps are in the declaration docstring.

Searches performed:
- msearch LeanFinder, query `Spec of universal square-zero ring extension is universal
  first order thickening of schemes`: eight hits, including FormallyUnramified,
  Scheme.Hom.liftQuotient, AffineSpace, and IdealSheafData gluing; no exact theorem.
- msearch Loogle, query `AlgebraicGeometry.Spec.map, Ideal.Quotient.mkₐ`: zero hits.
- msearch grep, query `universal.*[Tt]hickening|[Tt]hickening.*universal`, subdirectory
  AlgebraicGeometry: zero hits.
- msearch LeanSearch, query `Spec of a universal square zero algebra extension is a
  universal first order thickening of schemes`: unavailable, Internal Server Error.
- rg of the same universal/thickening expression in source WeilConjectures and
  project lean/Sheaf: the source has only a universal-homeomorphism comment; project
  hits include the universal-thickening definition and the ring existence theorem,
  neither stating this item. The latter was read to confirm the algebra-map encoding.
- grep for `lem-weil-pbc-universal-thickening-affine-case` in source WeilConjectures:
  no hits.
- rg for `isUniversalFirstOrderThickening_spec` in Mathlib, source WeilConjectures,
  project lean/Sheaf, and dag/lean_names_upstream.json: no hits before writing.

The local Stacks checkout is absent. The source was read at
https://stacks.math.columbia.edu/tag/04F3, especially the affine-case paragraph:
it reduces affine tests to the ring statement and extends to all tests by gluing.
The recorded node statement agrees with this argument. No node faults found.

## Second reading by V1

I read the node statement, its Stacks source (More on Morphisms, proof of Lemma 04F3,
third paragraph), the dependency declarations, and the Lean file item by item.
The objects are commutative rings `R`, `S`, `S'`; a ring map `φ : R →+* S`; an
`R`-algebra structure on `S'` and `S`; an `R`-algebra map `π : S' →ₐ[R] S`; and
`X = Spec R`, `Z = Spec S`, `Z' = Spec S'`. The Lean terms rendering these are
`R S S'`, `φ`, the two `Algebra` instances, and `π`. The coherence hypothesis
`hφ : algebraMap R S = φ` makes the selected Lean algebra structure on `S` the
one specified by the node's `φ`.

The hypotheses match as follows. Surjectivity is `hπ`; square-zero kernel is
`hK : RingHom.ker π.toRingHom ^ 2 = ⊥`; and the ring universal property is
`hUniversal`, quantifying over every `A : Type u`, square-zero ideal `I`, and
`a : S →ₐ[R] A ⧸ I`, with the exact `∃!` lift equation using
`Ideal.Quotient.mkₐ`. The source's arbitrary test-algebra convention is represented
at the same universe as the ring data, as required by the project scheme encoding.
The conclusion is exactly `IsUniversalFirstOrderThickening` applied to
`Spec.map (CommRingCat.ofHom φ)`, `Spec.map (CommRingCat.ofHom π.toRingHom)`,
and `Spec.map (CommRingCat.ofHom (algebraMap R S'))`; this expands to the closed
immersion with square-zero ideal sheaf, the commuting triangle, and the universal
lifting property for arbitrary (including non-affine and empty) test schemes.

I found one mismatch: the worker Lean omitted `φ`, used `algebraMap R S` in the
first structure morphism, and therefore did not state the node's arbitrary ring
map. I added `φ` and the necessary coherence `hφ`, and changed that `Spec.map`
term to `φ`. No other hypotheses or conclusion clauses changed. Zero rings,
zero ideals, empty spectra, empty index/test schemes, and all characteristics are
allowed; no finiteness, Noetherian, nonzero, or affineness assumption was added.

The existing-definition searches were rechecked: LeanFinder/LeanSearch and Loogle
found only generic `Spec`, quotient lifts, and formally-unramified lemmas; grep of
Mathlib, `WeilConjectures`, and project `lean/Sheaf` found no declaration of this
universal thickening statement. The dependency modules used are
`Sheaf.AlgebraicGeometry.UniversalFirstOrderThickening` and Mathlib's
`Ideal.Quotient.mkₐ`; no new definition or dependency module was needed.
