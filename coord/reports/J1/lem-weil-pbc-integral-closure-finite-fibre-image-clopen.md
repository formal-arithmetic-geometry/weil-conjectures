## Worker report

The module states the clopen-image and product-decomposition conclusion for a finite-type
commutative-ring map. `A`, `B`, and `I` render the source ring map and ideal; `C₁` and
`C₂`, `β`, `hβ`, `ε`, `hε`, and `hdecomp` render the fibre decomposition and finite
component; `U`, `T`, `hT`, `hiso`, and `hTβ` render the open neighbourhood, the inverse
image component, the isomorphism condition on the restricted spectrum map, and the
identification of `T`. The existential conclusion gives `ε'`, `C'₁`, `C'₂`, clopen
image, exact inverse image, product decomposition, and the isomorphism `C'₁ ≃+* C₁`.

Dependencies used are Mathlib `AlgebraicGeometry.Spec` (the affine spectrum and
`PrimeSpectrum.comap`) and Mathlib integral-closure definitions; the two DAG dependencies
are represented by these declarations. Edge cases include arbitrary commutative rings,
zero ideals, empty spectra, and empty components (all are permitted by the binders).
Searches in Mathlib and `WeilConjectures/` found no existing theorem combining these
claims; the node's recorded LeanSearch/Loogle/grep searches report no match.

## Earlier second reading (a previous round; superseded)

The statement was reread against the node clause by clause. The hypotheses bind the finite
 type map, fibre decomposition, open set, component, and restricted-spectrum bijection.
The conclusion explicitly contains openness and closedness, exact inverse image, a unique
idempotent witness, product decomposition, and the component ring isomorphism. No proof
content beyond `sorry` is present.

## Second reading by J1

Independent reading of the node, the original sandbox module, both statement-dependency
nodes and their Mathlib declarations, and Stacks `more-algebra.tex`, Lemma
`lemma-helper-finite-type` (Tag 09XH), especially the paragraphs on the image of `T`.
The literature directory is absent from this read-only clone; I read the Stacks source
copy `/home/ubuntu/c1-stacks-review/more-algebra.tex`, including the full lemma and proof.
The lemma assumes only a pair `(A,I)` and the displayed finite-type/product/finiteness
conditions. Its `U` is assembled from localization isomorphisms. Thus the node's
locally ringed space isomorphism over `U` is precisely the property used by the source,
not an added Noetherian, normal, domain, field, or nonempty hypothesis.

The original worker signature did NOT say the node's statement. The preceding worker
report and earlier second reading describe that original signature and are superseded
by the following clause-by-clause reading of the repaired signature.

Objects and hypotheses, with their Lean renderings and verdicts:

- Arbitrary commutative rings `A`, `B` and the finite-type ring map: `CommRing A`,
  `CommRing B`, `Algebra A B`, `Algebra.FiniteType A B`. PASS. An algebra structure
  records an arbitrary ring map; it does not assume injectivity.
- The ideal `I` and the closed fibre `B/IB`: `I : Ideal A`,
  `R := B ⧸ Ideal.map (algebraMap A B) I`, and `π := Ideal.Quotient.mk ...`. PASS.
- The chosen product `R = C₁ × C₂`: `e : R ≃+* C₁ × C₂`. PASS. The distinguished
  idempotent is exactly `e.symm (1,0)`; it is no longer an unrelated parameter.
- `C₁` finite for the induced `A/I`-action: `Algebra (A ⧸ I) C₁`,
  `Module.Finite (A ⧸ I) C₁`, and `hcompat`. PASS. The compatibility equation on
  every `a : A` fixes the action to the first projection of the given quotient
  decomposition. This spells out the structural map the source assumes.
- `B'` is the integral closure inside `B`: Mathlib `integralClosure A B`; `ι` is
  its inclusion `algebraMap (integralClosure A B) B`. PASS. I opened the definition:
  its carrier is exactly the elements satisfying `IsIntegral A`, with actual ring
  data and the induced `A`-algebra structure, not a postponed definition.
- `φ` is contraction along that inclusion: `φ := PrimeSpectrum.comap ι`. PASS.
- `T` is the image of the primes of `C₁` under the actual quotient projection:
  `β := (RingHom.fst C₁ C₂).comp (e.toRingHom.comp π)` and
  `T := Set.range (PrimeSpectrum.comap β)`. PASS. Neither a separate arbitrary
  surjection nor an arbitrary set is now being substituted for this component.
- The open neighbourhood `U`: `(Spec (.of (integralClosure A B))).Opens`. PASS;
  openness is carried by the type, unlike the original unconstrained set.
- The induced morphism over `U` is an isomorphism of locally ringed spaces:
  `hiso : IsIso (Spec.map (CommRingCat.ofHom ι) ∣_ U)`. PASS. I read
  `morphismRestrict`, which is the restriction onto the inverse image of `U`.
  Schemes form a full subcategory of locally ringed spaces, so this is the same
  isomorphism condition, including sheaf and stalk maps, not merely a point bijection.
- The component lies over `U`: `T ⊆ φ ⁻¹' U.1 → ...`. PASS. This final implication
  is the final hypothesis of the theorem; it precedes all existential conclusions.

Conclusions, with their Lean renderings and verdicts:

- The quotient `R' = B'/IB'` and its quotient map: `R'` and `π'` in the lets. PASS.
- The induced map `R' → R`: existential `f : R' →+* R` with
  `∀ b, f (π' b) = π (ι b)`. PASS. Surjectivity of `π'` uniquely determines it,
  so there is no unconstrained replacement for the inclusion-induced map.
- The image is open and closed in the closed fibre: the `IsClopen` assertion on
  `(PrimeSpectrum.comap π') ⁻¹' (φ '' T)` in `Spec R'`. PASS. The quotient-spectrum
  homeomorphism identifies this spectrum with `V(IB')`; ambient openness in
  `Spec B'` has been removed. The basic-open image equality below also states
  explicitly that `φ(T)` lies in the closed fibre.
- The inverse image of `φ(T)` is exactly `T`: `φ ⁻¹' (φ '' T) = T`. PASS.
- The idempotent and its exact image description: `ε' : R'`, `IsIdempotentElem ε'`,
  and `φ '' T = PrimeSpectrum.comap π' '' (PrimeSpectrum.basicOpen ε' : Set _)`.
  PASS. For each lift of `ε'`, contraction of a quotient prime omits that lift
  exactly when the quotient prime omits `ε'`. This is the node's lift-independent
  description `V(IB') ∩ D(lift ε')`.
- Uniqueness for that image description: `∀ δ : R', IsIdempotentElem δ →` the
  same basic-open image equality `→ δ = ε'`. PASS. This quantifies over all
  candidate idempotents, not just ones additionally satisfying factor-map clauses.
- The inclusion-induced quotient map sends the distinguished idempotent to the
  original one: `f ε' = e.symm (1,0)`. PASS.
- The resulting product decomposition: `C'₁`, `C'₂`, their `CommRing` structures,
  `e' : R' ≃+* C'₁ × C'₂`, and `e' ε' = (1,0)`. PASS. Under this decomposition,
  the ideal `ε'R'` identifies precisely with the first coordinate ring (identity
  `ε'`), and `(1-ε')R'` with the second. These are coordinate presentations of
  the stated factors, not separate unrelated rings.
- The actual first-factor map is a ring isomorphism and the second factor maps
  to the second factor: `g : C'₁ ≃+* C₁`, `h : C'₂ →+* C₂`, and
  `∀ r : R', e (f r) = (g (e' r).1, h (e' r).2)`. PASS. This commuting equation
  for every element forces `g` and `h` to be the induced component maps. In
  particular it is substantially more precise than an unrelated ring isomorphism.

Dependency audit: `def-weil-affine-spectrum` records Mathlib `AlgebraicGeometry.Spec`
(`Scheme.lean`) and `Spec.map`; I opened both declarations and the underlying
`Spec.topObj` / `Spec.topMap`. `def-weil-locally-ringed-space-morphism` records
`LocallyRingedSpace.Hom`; I opened its extending sheaf morphism and local stalk-map
field and `Scheme.Hom`. `Mathlib.AlgebraicGeometry.Restrict` supplies these declarations
and the standard restricted morphism, while
`Mathlib.RingTheory.IntegralClosure.Algebra.Basic` supplies the integral closure.
Both imports are used. No new definition nodes or dependency modules are needed.
All added notation in the theorem consists of local abbreviations for the existing
Mathlib operations, not new definitions of notions.

Edge cases: all four ring universes are explicit and independent (`A : Type v`,
`B : Type u`, `C₁ : Type w`, `C₂ : Type z`), with no restriction on the base ring's
universe. The existential factor rings use `Type u`, the universe of `R'`; idempotent
ideals of `R'` have presentations in that universe even when the given `C₁` is in
another universe, and `RingEquiv` permits this comparison. Zero rings and zero
components are allowed (no `Nontrivial` or domain assumptions). Empty spectra and
`U = ∅` are allowed: then `T = ∅` and the first factor is the zero ring. `I = ⊥`
and `I = ⊤` are allowed, as are every characteristic. There is no index set or
integer parameter to exclude empty indices or `n = 0`. No variable is auto-implicit.

Independent searches (2026-10-11):

- `msearch.py ... leanfinder "finite closed fibre component integral closure clopen
  image ring factor isomorphism"` returned eight ingredients, including
  `Algebra.ZariskisMainProperty`, `PrimeSpectrum.isClosedMap_comap_of_isIntegral`,
  and fibre-spectrum equivalences; none states this component theorem.
- `msearch.py ... loogle "PrimeSpectrum.isClosedMap_comap_of_isIntegral"` returned
  that declaration only. It proves closedness for an integral map, without the
  open image, idempotent uniqueness, or induced factor identification.
- `msearch.py ... grep "integralClosure.*(clopen|image)|finite.*[Ff]ibre.*(image|clopen)"`
  returned no relevant theorem. Independent `rg` searches for `finiteFibre`,
  `finite_fibre`, `image_clopen`, `clopen.*image`, `image.*clopen`, and
  `integralClosure.*[Ii]mage` in Mathlib, `WeilConjectures/`, and repository
  `lean/Sheaf/` found only unrelated fibre and clopen ingredients. I opened
  `PrimeSpectrum.exists_algebraMap_localization_eq_of_isClopen` in upstream
  `RingTheory/Spectrum/Prime/LocallyConstant.lean`: it supplies an element with
  prescribed localization values, not this result. I also opened Mathlib's
  `isIdempotentElemEquivClopens`, an ingredient and not the present theorem.
- The exact declaration and module names were searched in Mathlib, upstream,
  `dag/lean_names_upstream.json`, and `lean/Sheaf/`; there is no collision.

Repairs: the original arbitrary `β`, unrelated idempotent and unlinked product witness
were replaced by one chosen product equivalence and its actual projection. The finite
algebra action is explicitly linked to that projection. The arbitrary set `U` and bare
`Set.BijOn` were replaced by an open and a genuine restricted-scheme isomorphism.
Ambient openness was replaced by relative clopenness. The quotient map, precise
idempotent image, uniqueness, preservation of both factors, and induced first-factor
isomorphism were added. The declaration now uses the `AlgebraicGeometry` namespace,
explicit universes and the standard header; its docstring records all ten proof steps.
No mathematical node statement changed; there is no statement correction, no new node,
no hollow definition, and nothing proved beyond the single required `sorry` theorem.
The node's `lean.statement` is copied verbatim from the repaired signature.
Validation: required server `scompile.py` completed with exit code 0 and no warnings.
