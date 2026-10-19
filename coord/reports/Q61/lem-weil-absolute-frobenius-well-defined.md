## Worker report

The single new module `Sheaf.AlgebraicGeometry.AbsoluteFrobeniusWellDefined` states
`AlgebraicGeometry.absoluteFrobenius_well_defined` with one `sorry`. No theorem is proved and no
new definition is introduced. The node's natural-language statement and dependency lists are
unchanged. The result uses the published ring and scheme constructions, not a choice of an
unspecified map. No repair note exists for this item.

Source read: `literature/stacks-project/varieties.tex`, lines 7003–7049, Section Frobenii,
Definition `definition-absolute-frobenius` (03SM), its following paragraph, and the naturality
lemma. The source defines the identity on the space and powers on the structure sheaf; the node
expands its affine, open, germ and iterate descriptions. Also read the full published
`WeilConjectures/AlgebraicGeometry/AbsoluteFrobenius.lean` and the ring construction in
`WeilConjectures/Mathlib/Algebra/CharP/Lemmas.lean`. Those definitions include their actual data.

Hypotheses and clauses, matched individually:

- The prime number is `(p : ℕ) (hp : p.Prime)`. Rings in (i)/(ii) are arbitrary
  `(A : Type v) [CommRing A]` with `hA : (p : A) = 0`. They are quantified separately from
  the scheme: no characteristic scheme is required to obtain the ring assertions.
- The ring map is `iterateFrobeniusOfPrime A hp hA n`, using the repaired recorded dependency.
  At `n = 1` its pointwise value is `a ^ p`; the construction's full signature and docstring
  were read. For general `n` its value is `a ^ p ^ n`.
- Part (i), inverse image of every prime: `∀ P : Ideal A, P.IsPrime → Ideal.comap ... P = P`.
  The next conjunct explicitly asserts that `(Spec.map ...).base = 𝟙 _`, so the identity on
  the underlying continuous map is not confused with identity of the scheme morphism.
- Part (ii) adds exactly `[IsLocalRing A]` and concludes `IsLocalHom ...`. Mathlib's locality
  is reflection of units, equivalent to the maximal-ideal formulation for local rings.
- Part (iii) is quantified over `(X : Scheme.{u}) (hX : X.IsCharacteristic p)`.
  `Scheme.IsCharacteristic` is the recorded predicate: `p.Prime ∧ ∀ U, (p : Γ(X,U)) = 0`.
  It is used directly, including `hX.2 ⊤` for the published scheme construction.
- The morphism is `X.iterateFrobenius hp (hX.2 ⊤) n : X ⟶ X`. Its type is the recorded
  `Scheme.Hom`, extending `LocallyRingedSpace.Hom`. Its actual `base` is the identity and
  `c` is a natural transformation of ring-valued presheaves, hence a map of structure
  sheaves. The `c.app (op U)` equality identifies every component with the recorded ring
  power endomorphism. Thus naturality includes all restriction-compatibility equations,
  rather than postulating an arbitrary map. The next conjunct records section values.
- Its stalk map is `(X.iterateFrobenius ... n).stalkMap x s = s ^ p ^ n`. The source
  construction has definitionally identity base, so the domain is exactly the stalk at x.
  Locality is also explicit as `∀ x, IsLocalHom (...stalkMap x).hom`.
- Part (iv), the affine assertion, is the existential proof `hSpec` that p vanishes in
  the affine global sections, followed by equality of `Scheme.iterateFrobenius` and
  `Spec.map (CommRingCat.ofHom (iterateFrobeniusOfPrime ... n))`. This only introduces the
  proof required by the canonical existing constructor; it assumes no extra datum.
- Open restriction is `∀ U, ∃ hU, (...).resLE U U le_rfl = U.toScheme.iterateFrobenius ... n`.
  The supplied Mathlib `Scheme.Hom.resLE` is the canonical restricted scheme morphism.
  Its inclusion proof is definitionally `le_rfl` because the Frobenius base is identity.
- An arbitrary affine chart is `(e : U.toScheme ≅ Spec (CommRingCat.of A))` and the last
  conjunct asserts the conjugation equality with `Spec.map` on that very chart. The
  vanishing of p in A is an output `∃ hA`, not an added hypothesis.
- Every clause is quantified over all `n : ℕ`, hence includes `n = 1` and the entire
  iterate statement. The ring function-iterate formula is included using `^[n]`.
  The scheme formula equates the construction at n to the nth power in `End X` of the
  construction at 1. `HPow.hPow` is explicit because elaborating ordinary power notation
  against the scheme-Hom equality otherwise erases the `End` instance. It is the ordinary
  monoid power, including identity at zero. Prime inverse images, locality, section and
  stalk powers, open restrictions, affine equality and arbitrary affine-chart equality
  all occur within the same universal n scope.

Dependency interfaces used and read:

- `def-weil-ring-frobenius`: repaired to `iterateFrobeniusOfPrime` and its application lemma
  in `WeilConjectures.Mathlib.Algebra.CharP.Lemmas` (see below).
- `def-weil-scheme-characteristic-p`: `AlgebraicGeometry.Scheme.IsCharacteristic` in
  `Sheaf.AlgebraicGeometry.SchemeCharacteristic`, including its docstring and full body.
- `def-weil-locally-ringed-space-morphism`: its `mathlib_match`,
  `AlgebraicGeometry.LocallyRingedSpace.Hom`, in
  `Mathlib.Geometry.RingedSpace.LocallyRingedSpace`. It is a Mathlib leaf, not a missing
  dependency. Read its inherited `PresheafedSpace.Hom` fields, local stalk condition,
  stalkMap, identity and composition. No wrapper for this notion is delivered.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map` in
  `Mathlib.AlgebraicGeometry.Scheme`; full declarations and docstrings read.
- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom` in the same module;
  read the local affine property and inheritance from locally ringed-space morphisms.
- `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion` in
  `Mathlib.AlgebraicGeometry.OpenImmersion`. Open subschemes and canonical restriction
  use `Scheme.Opens.toScheme` and `Scheme.Hom.resLE` from `Mathlib.AlgebraicGeometry.Restrict`.
  These imported modules include every stated statement/proof dependency; none is omitted.

Edge cases: the zero ring is allowed by `(p : A) = 0`, and its spectrum is empty. The zero
ring of sections over the empty open and the empty scheme are allowed throughout; no
`Nontrivial`, `ExpChar` or field assumption was imposed. `n = 0` gives exponent one and
identity morphisms, while `n = 1` is the original Frobenius. Nonreduced rings and schemes are
included: no injectivity, reducedness or perfection hypothesis appears. Universes u and v
are explicit and independent, with no quantification over potentially absent test algebras.
The affine chart ring lies in the scheme's object universe. There is no statement dispute.

Searches actually run:

- `msearch.py ... leansearch` with “The absolute Frobenius of a scheme is the identity on
  points and raises sections to pth powers, is local on stalks, agrees with Spec on affine
  schemes, and commutes with restrictions”: eight hits, including ring Frobenius,
  `stalkwise` and `localRingHom_comp_stalkIso_apply`; no combined scheme assertion.
- `msearch.py ... leanfinder` with “Frobenius of a scheme fixes prime ideals and is a local
  ring homomorphism, agrees with Spec of ring Frobenius and restricts to opens”: eight
  hits on arithmetic Frobenius at a prime and perfect-ring Frobenius; no exact assertion.
- `msearch.py ... loogle 'frobenius, Ideal.comap'`: zero hits.
- `msearch.py ... grep 'frobenius|Frobenius' AlgebraicGeometry`: zero Mathlib hits.
- `rg` over the prescribed upstream `WeilConjectures` and project `lean/Sheaf` for
  Frobenius/absolute Frobenius found the published real construction in AbsoluteFrobenius
  and uses in RelativeFrobeniusGeometricFiber, but no theorem with all clauses.
- The exact item-id search in upstream yielded no declaration. Searching
  `dag/lean_names_upstream.json` found ring Frobenius names and unrelated arithmetic
  Frobenius statements, but no exact statement for this node. The proposed theorem name
  was searched in both source trees and was absent.

Validation: the delivered module compiles cleanly through `scompile.py` in both the isolated
sandbox and library-name passes. All variables and universes are explicitly bound. The only
new theorem is the named `sorry` statement, with all nine proof steps in its docstring.

## Dependency modules

`def-weil-ring-frobenius` receives a lean-only existing-declaration repair under §1(B).
Its Mathlib match requires `ExpChar A p` and explicitly excludes the zero ring, so it cannot
serve the empty-open clause of the item. The already published
`iterateFrobeniusOfPrime` in `WeilConjectures.Mathlib.Algebra.CharP.Lemmas` instead takes exactly
primality and `(p : A) = 0`, permits the zero ring, and constructs the actual ring map for every
n. At n=1 this is the node's ordinary Frobenius; the application lemma gives the powers.
Naturality is the ring-hom `map_pow` equation. The repair records these existing declarations,
not a second definition. Its `lean.note` explains the unusable old interface. Every other field
of the dependency node, including its Mathlib match and status, is preserved.

The initial draft unnecessarily wrapped both the ring map and locally ringed-space morphisms.
Those wrappers and their modules were removed before validation. The latter dependency already
has the exact usable Mathlib match `LocallyRingedSpace.Hom` and receives no node edit.

## Second reading by Q61

I read the item node `lem-weil-absolute-frobenius-well-defined`, its source place in
`literature/stacks-project/varieties.tex` (Section 33.36, Tag 03SM and the paragraph after
Definition 33.36.1), and every recorded statement dependency. The node introduces the prime
`p` with `p.Prime`; a commutative ring `A` with `(p : A) = 0` and its Frobenius
`a ↦ a^p`; a scheme `X` of characteristic `p`; and open subschemes and affine charts.
Its clauses are: (i) Frobenius inverse images of prime ideals are unchanged and the induced
map on `Spec` is the identity; (ii) Frobenius is local on a local ring; (iii) the sectionwise
maps form a sheaf endomorphism, induce the stated stalk Frobenius, and give an identity-on-space
scheme endomorphism; (iv) the affine `Spec` formula, restriction to opens, affine-chart formula,
and the corresponding iterate formulas `a ↦ a^(p^n)`.

The Lean signature renders these items as follows. The ring binder
`(A : Type v) [CommRing A] (hA : (p : A) = 0)` is exactly the node's arbitrary commutative
ring, including the zero ring. `iterateFrobeniusOfPrime A hp hA n` is the recorded repaired
Frobenius/iterate map, so its prime-ideal comap equality and `Spec.map` base identity render
(i), while the `IsLocalHom` conjunct renders (ii). The section formula
`(X.iterateFrobenius hp (hX.2 ⊤) n).app U s = s ^ p ^ n`, stalk formula, and identity base
render (iii) for every iterate. The `resLE` equality and affine-chart conjugation render the
open and affine parts of (iv); the ring-side `Spec` equality renders the affine whole-scheme
case. The universal `n : ℕ` binders include `n = 0` and `n = 1` and all higher iterates.
No additional ring, scheme, finiteness, reducedness, or characteristic hypothesis is present.

The first worker's signature also asserted three implementation-level consequences beyond the
node's clauses: equality of every natural-transformation component `c.app`, an explicit separate
stalk-locality proposition, and an equality in `End X` with a monoid power. Those are stronger
than the node's statement (the scheme-hom type already carries locality, and the section/stalk
clauses state the requested maps). I removed those three conjuncts, retained all node clauses,
and updated the node's `lean.statement` verbatim to the repaired signature. The theorem remains a
single named `sorry`; no definition is hollow and no proof was added.

Edge cases checked: the zero ring and empty spectrum/opens are admitted by `[CommRing A]` and
`(p : A) = 0`; the empty scheme satisfies `IsCharacteristic`; `n = 0` gives the identity and
`n = 1` gives ordinary Frobenius; nonreduced rings and schemes are included; and the ring and
scheme universes `v` and `u` are explicit and independent. The affine-chart ring is correctly
in `Type u` for `Scheme.{u}`.

I repeated the three required searches. `msearch.py` LeanSearch, LeanFinder, and Loogle queries
for an absolute-Frobenius scheme theorem found only ring/perfection ingredients or no result;
`rg` over Mathlib AlgebraicGeometry, the upstream `WeilConjectures` tree, and project `lean/Sheaf`
found no declaration of this combined statement. The published construction
`WeilConjectures.AlgebraicGeometry.Scheme.iterateFrobenius` and its section formula were read and
used; the dependency repair for `def-weil-ring-frobenius` was checked against
`iterateFrobeniusOfPrime`, which permits the zero ring unlike Mathlib's `ExpChar` interface.

Validation: `python3 /home/ubuntu/weil-launcher-nt/scompile.py Q61
lem-weil-absolute-frobenius-well-defined
lean/Sheaf/AlgebraicGeometry/AbsoluteFrobeniusWellDefined.lean` succeeds with no errors or
warnings.

## Maintainer review fix

The second reading removed the conjunct equating the scheme construction at `n` with the
`n`-th power in `End X` of the construction at `n = 1`, calling it stronger than the node.
That is not right. The node's final sentence and its proof step 9 are about the iterates,
i.e. the `n`-fold composites of `(id_X, F^♯)`. The definition node
def-weil-absolute-frobenius-scheme also defines the q-power Frobenius as that composite.
Without the conjunct, the scheme clauses describe only the published construction indexed by
`n`, never the composite. The reviewer restored the clause as
`HPow.hPow (α := End X) (X.iterateFrobenius hp (hX.2 ⊤) 1) n = X.iterateFrobenius hp (hX.2 ⊤) n`.
It is the monoid power, so `n = 0` gives `𝟙 X`. It matches the ring-side conjunct
`(iterateFrobeniusOfPrime A hp hA 1)^[n] a = a ^ p ^ n`, which was kept. Proof step 9 in the
docstring now says this. The worker report above still mentions the explicit `c.app` and
stalk-locality conjuncts. Those stay removed: `app` and `Scheme.Hom` locality already cover them.
