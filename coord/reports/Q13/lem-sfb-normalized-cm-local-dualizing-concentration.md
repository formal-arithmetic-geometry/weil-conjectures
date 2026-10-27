## Worker report

The module `Sheaf.Algebra.Homology.NormalizedCMDualizingConcentration` states
`DerivedCategory.normalizedCMDualizing_concentration`, with its sole proof `sorry`.
It introduces no definitions, helper theorems, or extra nodes. The node is unchanged
except for its `lean` record. Sources read: Stacks `dualizing.tex`,
lemma-apply-CM (0AWS) and lemma-depth-dualizing-module (0AWE).

Hypothesis-by-hypothesis correspondence:

- A nonzero commutative Noetherian local ring: `A : Type u`, `[CommRing A]`,
  `[IsNoetherianRing A]`, `[IsLocalRing A]`. Mathlib's `IsLocalRing` extends
  `Nontrivial A`, so nonzeroness is included without a redundant instance.
- Finite Krull dimension d: `(d : ℕ)` and
  `hdim : ringKrullDim A = (d : WithBot ℕ∞)`.
- Cohen–Macaulay condition: `hdepth : IsLocalRing.depth (R := A) A = (d : ℕ∞)`.
- K in D(A): `K : DerivedCategory (ModuleCat.{u} A)`, using the same existing
  ordinary-module derived-category instances as the depth-detection dependency.
- A bounded injective representative: `hKinjective` supplies a cochain complex J,
  integers a,b with `IsZero (J.X i)` for `i < a ∨ b < i`, termwise `Injective`,
  and `Nonempty (Q.obj J ≅ K)`. This is strict boundedness of a representative,
  not merely bounded cohomology.
- Every cohomology module finite: `hKfinite : ∀ i : ℤ, Module.Finite A
  ((homologyFunctor (ModuleCat.{u} A) i).obj K)`.
- The canonical scalar action is an isomorphism: `hKscalar : IsIso
  (MonoidalClosed.id K)`. This existing morphism is the transpose of the right
  unitor, with source the derived tensor unit representing A[0] and target
  RHom(K,K); it is the homothety map, not an arbitrary isomorphism.
- Residue field normalization: `hKnormalized` is an isomorphism between
  `(ordinaryModuleDerivedInternalHom A).obj (op (κ[0]), K)` and κ[0], with
  `κ = A ⧸ IsLocalRing.maximalIdeal A` and the degree-zero embedding written
  using `singleFunctor`.

Conclusion-by-conclusion correspondence (write W = H^(-d)(K) just for this report):

- W is exactly `(homologyFunctor (ModuleCat.{u} A) (-(d : ℤ))).obj K` throughout.
  No existential replacement module or unrelated cohomology object is used.
- K is isomorphic to W[d]: the first conjunct is `Nonempty (K ≅
  ((singleFunctor (ModuleCat.{u} A) 0).obj W)⟦(d : ℤ)⟧)`.
  The existing shift is the cohomological shift `(L[d])^j = L^(j+d)`.
- W is nonzero: `Nontrivial W`, appropriate for the underlying module.
- W is finitely generated: `∃ hWfinite : Module.Finite A W, ...`.
  The existential witness is a proof of finite generation only.
- Full support: `∀ p : PrimeSpectrum A, Nontrivial
  (LocalizedModule p.asIdeal.primeCompl W)`. This is literally the nonzero
  localization at every prime, equivalently Mathlib's `Module.support A W = Set.univ`.
- Depth W equals d: `@IsLocalRing.depth A _ _ W _ _ hWfinite = (d : ℕ∞)`.
  The explicit proof argument uses the finite-generation conclusion to type depth;
  it does not assume finite generation or the claimed depth as an extra hypothesis.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`.
- `WeilConjectures.RingTheory.Depth`: `Ideal.depth`, `IsLocalRing.depth`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic` and `.HomologySequence`:
  `DerivedCategory`, `DerivedCategory.Q`, `DerivedCategory.singleFunctor`,
  `DerivedCategory.homologyFunctor` (the public homology import exposes these).
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`.
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic`: `CategoryTheory.Injective`.
  The node needs injective terms; it does not ask for an injective resolution of
  a module in degree zero.
- `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom`:
  `CategoryTheory.ordinaryModuleDerivedInternalHom`, the dependency's recorded
  ordinary-module specialization, not a newly constructed RHom.
- `Mathlib.CategoryTheory.Monoidal.Closed.Basic`: `MonoidalClosed.id`, provided
  by the existing closed derived tensor structure in the RHom dependency.

Proof dependencies are imported with plain imports: the K-injective theorem
`CochainComplex.isKInjective_of_injective` from
`Mathlib.Algebra.Homology.HomotopyCategory.KInjective`; the recorded Hom complex
from `WeilConjectures.Algebra.Homology.HomComplex`; the support-annihilator
lemmas `Module.mem_support_iff_of_finite` and `Module.support_eq_zeroLocus` from
`Mathlib.RingTheory.Support`; and
`DerivedCategory.normalizedDualizing_degreeBounds_depthDetection` from
`Sheaf.Algebra.Homology.NormalizedDualizingDepthDetection`. The theorem's
source-and-blueprint docstring records all four accepted proof steps, including
the good truncation zigzag, annihilator argument, and Hom shift signs.

Edge cases checked: d=0 retains W=H^0(K) and the zero shift, covering Artinian
local rings including fields. No reduced, domain, equicharacteristic, complete,
or Gorenstein hypothesis is added. The zero ring is already excluded by the
node and `IsLocalRing`. The zero complex cannot satisfy normalization since κ
is nonzero. Negative cohomological degrees use integer negation of d, not natural
subtraction. Prime localization includes both minimal and maximal primes. The
universe u is arbitrary and matches the existing ordinary-module RHom interface.

Searches on 2026-10-24:

- `msearch.py ... leanfinder`: “Normalized dualizing complex over a Cohen Macaulay
  local ring is its canonical module shifted by Krull dimension with full support
  and depth equal dimension”. Eight hits, all support-dimension results, including
  `Module.supportDim_self_eq_ringKrullDim` and `Module.supportDim`; no match.
- `msearch.py ... loogle '"dualizing"'`: zero hits.
- `msearch.py ... grep 'dualizing|dualising|CohenMacaulay' RingTheory`: zero hits.
- `msearch.py ... leansearch`: “Normalized dualizing complex of a Cohen Macaulay
  local ring is a shifted maximal Cohen Macaulay module”. Eight hits concerning
  ordinary dual modules, cotangent spaces, or perfect pairings; no match.
- `rg` of `lean/WeilConjectures` for dualizing/dualising/CohenMacaulay found
  geometric and étale dualizing complexes and Cohen–Macaulay free resolutions,
  not this local normalized-dualizing theorem. Search for this node id there
  returned no hits.
- `rg` of `lean/Sheaf`, narrowed to the algebra/Homology family after the broad
  search, found `NormalizedDualizingDepthDetection`, whose existing declaration
  supplies the proof tool rather than the concentration conclusion.
- `rg` of `dag/lean_names_upstream.json` for the proposed name and canonical-module
  or normalized-duality names found no matching local-ring theorem; canonical
  modules of projective space are unrelated.

No statement fault or dispute was found. The former example
`Sheaf.CategoryTheory.CompactObject` is now a withdrawn module; its node points
to `WeilConjectures.CategoryTheory.CompactObject`, confirming the current
one-definition convention rather than suggesting a duplicate definition.

## Second reading by Q13

Author's second reading, with the node, source, and completed file open; independent
review is supplied by the maintainer, as the dispatcher brief specifies. Checked
all seven ring/complex hypotheses and all five module/isomorphism conclusions
against the correspondences above. In particular, the finite-generation witness
only supplies the existing depth API's required proof, and the support clause
quantifies over every prime. The dimension-zero and shift-sign cases agree with
0AWS. No mismatch was found and no statement correction was made. No second agent
was started.

Validation: the prescribed `scompile.py` compiled both its sandbox probe and the
library-path module cleanly (3.3 s and 4.0 s). Only the statement is postponed.
