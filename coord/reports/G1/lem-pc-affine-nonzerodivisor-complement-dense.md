## Worker report

The module states the two conclusions of the affine calculation in Stacks Project,
Divisors, Lemma 31.14.4 (Tag 07ZU). Its only theorem has a `sorry` proof.

- The arbitrary commutative ring is `(A : Type u) [CommRing A]`; no nontriviality,
  reducedness, domain, or finiteness condition is imposed.
- The chosen element and its nonzerodivisor hypothesis are `(a : A)` and
  `(ha : a ∈ nonZeroDivisors A)`.
- The affine scheme `X = Spec A` is `Spec (.of A)`. The principal open `U = D(a)` is
  `PrimeSpectrum.basicOpen a`, and its inclusion `j` is `Scheme.Opens.ι
  (X := Spec (.of A)) (PrimeSpectrum.basicOpen a)`.
- Injectivity of the sheaf map `O_X → j_* O_U` is rendered by `∀ V : (Spec
  (.of A)).Opens, Function.Injective (j.app V)`. This asks for injectivity on every
  open, including the empty open, exactly the componentwise criterion for an
  injective morphism of sheaves of rings.
- Topological density of `U` in `X` is `DenseRange j`; the inclusion's image is
  precisely the underlying subset of `D(a)`.

Statement dependency: `def-pc-scheme` is Mathlib's
`AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`, declared in
`Mathlib.AlgebraicGeometry.Scheme`. The module uses `Spec`,
`PrimeSpectrum.basicOpen`, and `Scheme.Opens.ι` from Mathlib and imports
`Mathlib.AlgebraicGeometry.Restrict` for the inclusion. No private duplicate
of a dependency is introduced.

The docstring records both DAG proof steps: localization on every principal
open, using `lem-pc-localization-preserves-nonzerodivisor` and
`lem-pc-affine-localization-injective`, followed by density from
`lem-pc-principal-open-dense-of-nonzerodivisor`.

Edge cases: `a = 1` makes `D(a)` all of `Spec A`; the zero ring has empty
spectrum, and the statement still includes it. In a nonzero ring `a = 0` is
excluded by the nonzerodivisor hypothesis. A zero divisor such as `x` in
`k[x,y]/(xy)` is excluded; its principal open need not be dense.

Searches for an existing declaration:

- `msearch leanfinder`, query "non-zero-divisor principal open D(a)
  scheme-theoretically dense restriction structure sheaf pushforward injective":
  eight related hits, none stating both conclusions.
- `msearch loogle`, query `Scheme.Hom.isDense,IsSchemeTheoreticallyDominant`:
  no hits; the first name was unknown.
- `msearch grep` in Mathlib AlgebraicGeometry, query
  `IsSchemeTheoreticallyDominant|SchemeTheoreticallyDense|DenseRange|Dense.*basicOpen|BasicOpen.*Dense`:
  found general dominance infrastructure, no theorem about this principal open.
- `rg` in Mathlib AlgebraicGeometry for basic-open density and sheaf injection:
  found the general scheme-theoretic dominance class and open-inclusion API,
  but no matching statement.
- `rg` and `grep -rn` in `WeilConjectures/` for the node id and concept:
  no matching declaration; broader hits concern compactifications.
- `rg` in project `lean/Sheaf/` for density and scheme-theoretic dominance:
  no matching declaration.
- `rg` in `dag/lean_names_upstream.json`, Mathlib, and `WeilConjectures/` for
  the chosen full name: no collision.

The local `literature/stacks-project/divisors.tex` is not present in this
checkout. I read the source place at https://stacks.math.columbia.edu/tag/07ZU;
it gives the affine calculation `A ⊆ A_f` for a nonzerodivisor `f`.

Server single-file compile: clean, 1.5 seconds.

## Second reading by G1

Independent comparison with the node and Stacks Project, Divisors, Lemma 31.14.4
(Tag 07ZU), including its affine-local proof:

- Object $A$, an arbitrary commutative ring: `(A : Type u) [CommRing A]`.
  Verdict: exact; no domain, nontriviality, reducedness, or finiteness assumption.
- Object $a \in A$ and hypothesis that it is a nonzerodivisor: `(a : A)
  (ha : a ∈ nonZeroDivisors A)`. Verdict: exact.
- Object $X=\operatorname{Spec}(A)$: `Spec (.of A)`. The dependency
  `def-pc-scheme` records Mathlib's `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom`; `Spec` constructs that scheme. Verdict: exact.
- Object $U=D(a)$ and its inclusion $j:U\to X$:
  `PrimeSpectrum.basicOpen a` and `Scheme.Opens.ι (X := Spec (.of A))
  (PrimeSpectrum.basicOpen a)`. The latter is the canonical open immersion
  from the open subscheme. Verdict: exact.
- Conclusion $\mathcal O_X\to j_*\mathcal O_U$ injective: `∀ V : (Spec
  (.of A)).Opens, Function.Injective (j.app V)`, with the inclusion expanded
  in the actual signature. `j.app V` is the induced map on sections over $V$.
  Verdict: exact componentwise injectivity, including the empty open.
- Conclusion $U$ topologically dense in $X$: `DenseRange j`, with the same
  inclusion expanded. Its image is $D(a)$. Verdict: exact.

The source proof assumes no additional global hypotheses. There is no index set
or natural-number parameter. `a = 1` gives the whole spectrum; for the zero
ring, the spectrum is empty and the statement remains included. In a nonzero
ring `a = 0` fails the hypothesis. All characteristics and universe levels of
the ring type are covered by `Type u` and `CommRing A`.

Independent searches: `msearch leanfinder` for "nonzerodivisor principal open
scheme theoretically dense sheaf restriction injective" returned related
structure-sheaf/basic-open results, but no matching conjunction. `msearch
loogle` for `PrimeSpectrum.basicOpen DenseRange nonZeroDivisors` returned no
match (the query did not parse as a type). `msearch grep` for
`basicOpen.*dense|dense.*basicOpen|nonZeroDivisors.*Scheme` returned no match.
Direct `rg` across Mathlib AlgebraicGeometry, source `WeilConjectures/`, and
project `lean/Sheaf/` found no declaration with this statement or full name.
The source's `Scheme.IdealSheafData.IsInvertible.isSchemeTheoreticallyDominant_compl_support`
is a theorem about an invertible ideal sheaf, not this affine ring statement.

No mismatch was found; the Lean module and node record required no change.
The declaration has only a `sorry` proof, and its docstring follows both node
proof steps and names all three proof dependencies.
