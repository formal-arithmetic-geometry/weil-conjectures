## Worker report

The new module `Sheaf.AlgebraicGeometry.FrobeniusFactorization` states
`WeilConjectures.FiniteFieldDatum.absoluteFrobenius_factorization`, with `sorry`
as its entire proof. There are no new definitions or dependency repairs, and the
node changes only in `lean`.

The node was read alongside the current main-20261015 blueprint statement and proof,
order 2416, in `sec-six-functors-basics/sk-prop-sf-rf-shriek-preservation`.
Its expanded three-step proof is reproduced in the theorem docstring.

Hypotheses and clauses:

- The global datum `(p,a,q,k₀,k)` is the binder
  `D : WeilConjectures.FiniteFieldDatum.{u}`. Its fields enforce primality,
  `1 ≤ a`, `q = p^a`, a finite field of cardinality q, and its fixed algebraic closure.
- A finite-type k₀-scheme is
  `X₀ : Over (Spec (CommRingCat.of D.k₀))`, with
  `[LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]`. This is exactly the
  dependency's finite-type convention, including nonseparated and nonreduced schemes.
- `X = X₀ ×_{k₀} k` is `(D.geometricFiber X₀).left`, the recorded pullback.
- The arithmetic coefficient automorphism `g_sigma` is precisely
  `D.arithmeticGaloisFrobenius X₀`. Reading its construction shows it is the inverse
  of the geometric coefficient action, hence id × Spec(z ↦ z^q), with the correct sign.
- `Phi` is `D.schemeFrobenius X₀`, the existing scalar extension of model Frobenius;
  `D.schemeFrobeniusIterate X₀ m` is its m-fold End power.
- Every integer m ≥ 1 is `(m : ℕ) (hm : 1 ≤ m)`. Natural numbers with this lower
  bound encode exactly the stated positive integers.
- Absolute q^m-power Frobenius is `Scheme.iterateFrobenius` with `D.prime`, the
  characteristic proof obtained by `D.model_characteristic` from the first projection
  composed with `X₀.hom`, and iteration count `D.a * m`. Thus its section formula is
  `s ↦ s^(p^(a*m)) = s^(q^m)`; on a pure tensor it is
  `u ⊗ b ↦ u^(q^m) ⊗ b^(q^m)`. This affine description identifies the named map,
  rather than imposing an additional conclusion about a newly introduced map.
- The first conjunct is absolute Frobenius = Phi^m ≫ g_sigma^m, rendering
  `g_sigma^m ∘ Phi^m`. The second is absolute Frobenius = g_sigma^m ≫ Phi^m,
  rendering the other composition order. Each coefficient power uses explicit
  `HPow.hPow (α := End ...)`, avoiding accidental inference of a power on a raw Hom.
- The equalities are equalities of the underlying scheme morphisms. The recorded maps
  are all over k₀ by construction (model Frobenius is over k₀, coefficient action fixes
  k₀, and absolute q^m-power acts identically on k₀). Forgetting from Over is faithful;
  equality of their underlying arrows is exactly equality of these k₀-arrows. No
  k-linearity is imposed on absolute or arithmetic Frobenius.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` and
  `WeilConjectures.FiniteFieldDatum.geometricFiber` (full structure and body read).
- `Sheaf.SixFunctors.SchemeFrobenius`:
  `WeilConjectures.FiniteFieldDatum.schemeFrobenius`, `schemeFrobeniusIterate`, and
  `arithmeticGaloisFrobenius` (full signatures and bodies read). Their implementations
  were followed into `Sheaf.AlgebraicGeometry.RelativeFrobeniusGeometricFiber` and
  `Sheaf.AlgebraicGeometry.FrobeniusDetailed`, including `relativeFrobenius`,
  `model_characteristic`, `galoisMap`, and `geometricFrobenius`.
- `WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius`:
  `AlgebraicGeometry.Scheme.iterateFrobenius`, `iterateFrobenius_app_apply`; this
  construction works even for the zero ring of sections.
- Proof-only imports follow all recorded proof dependencies:
  `WeilConjectures.Mathlib.Algebra.CharP.Lemmas` (`iterateFrobeniusOfPrime`),
  `Mathlib.LinearAlgebra.TensorProduct.Defs` (`TensorProduct`),
  `Mathlib.AlgebraicGeometry.Scheme` (`Spec`, `Spec.map`), and
  `Mathlib.Geometry.RingedSpace.LocallyRingedSpace` (`LocallyRingedSpace.Hom`).
  Their recorded declarations and docstrings were opened in source.

Edge cases checked: the empty model is allowed, because characteristic is expressed
by p = 0 on global sections, without ExpChar or nontriviality; nilpotent charts remain
included since no reducedness hypothesis occurs. On Spec k₀, Phi is the identity and
absolute Frobenius is the arithmetic coefficient map. On affine line the two factors
raise the coordinate and coefficient respectively. On k₀[e]/(e²), the same pure-tensor
calculation includes nilpotents. The allowed boundary m=1 gives exactly the source's
first factorization. m=0 is deliberately not asserted, matching the node. No additional
prime, coefficient-field, smoothness, or separatedness hypothesis is present.

Searches (2026-10-17):

- msearch LeanFinder, `factorization absolute q power Frobenius geometric fiber`:
  eight hits concerning arithmetic Frobenius at primes, Witt vectors and perfect
  closures; no scheme-factorization statement.
- msearch Loogle, `schemeFrobenius, arithmeticGaloisFrobenius, iterateFrobenius`:
  zero hits; unknown identifier `schemeFrobenius` in its Mathlib index.
- msearch LeanSearch, `Absolute Frobenius of a tensor product is the product of
  Frobenius on the two factors`: eight hits, including TensorProduct.map_pow,
  tensor map multiplication and LinearMap.frobenius; none is the scheme theorem.
- msearch grep, `frobenius factorization` under `WeilConjectures`: zero hits;
  msearch grep `[Ff]robenius` under Mathlib `AlgebraicGeometry`: zero hits.
- Direct rg over upstream WeilConjectures and side Sheaf for `schemeFrobenius`,
  `arithmeticGaloisFrobenius`, `iterateFrobenius`, and factorization names found the
  definitions above and `PurityFiniteSetting.schemeGeometricFrobenius_factorization`
  in `Sheaf.SixFunctors.SchemeGeometricFrobenius`. Its full statement was read: it
  assumes a purity datum (including coefficients), treats only m=1, and adds the
  geometric factorization, so is not an exact existing statement for this node.
- rg for the item id in upstream WeilConjectures found no declaration; rg for
  factorization names in `dag/lean_names_upstream.json` found no match.

No statement dispute or node fault was found. The first wrapper compile exposed
power-type inference/precedence errors; the explicit End power fixed them. The final
`scompile.py Q159 prop-trf-frobenius-factorization
lean/Sheaf/AlgebraicGeometry/FrobeniusFactorization.lean` compiled both sandbox and
library module cleanly, with no warnings or errors.

## Second reading by Q159

Author's second reading (the maintainer performs the independent review): I reopened
both the node and completed Lean file. The datum, bundled base scheme and two finite-type
instances match every setup hypothesis; the positive m binder neither excludes m=1 nor
includes m=0. The exponent a*m matches (p^a)^m, rather than p^m or q*m. The two conjuncts
both use the same absolute morphism and reverse the displayed factors exactly as
required by Lean's left-to-right composition. `arithmeticGaloisFrobenius` uses the inverse
of geometric Frobenius, and its End power is genuine iteration. I checked that no
coefficient datum leaked in from the larger imported module. The affine clause is
already the semantics of the recorded absolute map, and equality of underlying arrows
expresses equality over k₀ because all arrows have the required structure-map equation.
No mathematical mismatch or source/node change was needed. Only the elaboration of the
coefficient powers changed after the first compile.
