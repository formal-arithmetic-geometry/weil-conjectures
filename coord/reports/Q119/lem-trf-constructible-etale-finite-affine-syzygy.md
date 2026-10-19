## Worker report

The module `Sheaf.AlgebraicGeometry.ConstructibleEtaleFiniteAffineSyzygy` states
`AlgebraicGeometry.Scheme.exists_constructible_etale_finite_affine_syzygy`, with
whole proof `sorry`. No definitions, auxiliary theorems, new nodes, dependency
repairs, or statement corrections are needed. Only the item's `lean` field changes.

The signature renders the node as a finite tower of short exact sequences. This
retains the individual kernel/epimorphism data and is an equivalent encoding of
the stated iterative construction and its spliced exact sequence, rather than
merely asserting that some unstructured resolution exists.

Hypotheses and clauses:

- The scheme is `(X : Scheme.{u})`; quasi-compactness and quasi-separatedness are
  `[CompactSpace X] [QuasiSeparatedSpace X]`. These are exactly the conventions
  used by the recorded finite-zero-cokernel dependency.
- The finite commutative coefficient ring is `(Λ : Type (u + 1)) [CommRing Λ]
  [Finite Λ]`. There is no nonzero-ring or characteristic restriction.
- `F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)` is a sheaf of modules
  over the constant coefficient ring on the small etale site, in the encoding
  explicitly prescribed by `def-weil-pbc-etale-sheaves` for constructible material.
  `hF : IsConstructibleEtaleModuleSheaf F` is the exact recorded constructibility
  predicate, including constructible locally closed parts and finite module values.
- The integer length `r >= 1` is `(r : ℕ) (hr : 1 ≤ r)`. Positive integers and
  positive natural numbers give the same lengths; negative and zero integers
  are outside the node's quantifier.
- `K : Fin (r + 1) → Sheaf ...` contains precisely `K_0,...,K_r`, and `K 0 = F`
  gives the prescribed starting term, with no arbitrary isomorphism substituted.
- `n : Fin r → ℕ` and `U : ∀ a, Fin (n a) → X.Etale` give one finite etale
  family for each step `a = 0,...,r-1`. Membership in `X.Etale` includes the
  etale structure morphism. `IsAffine (U a t).left` asserts affineness of each
  source scheme. The node's `U_{a+1,t}` is the signature's `U a t`.
- `E : Fin r → Sheaf ...` and the equality for every `E a` identify it literally
  with the finite coproduct of
  `(Etale.etaleLowerShriek ... (U a t).hom inferInstance).obj
  ((constantSheaf ...).obj (ModuleCat.of Λ Λ))`.
  In this abelian category a finite coproduct is the direct sum. The summands
  are precisely `j_{U_{a+1,t}!} Λ_{U_{a+1,t}}`, using the recorded functor and
  the constant rank-one module, not free presheaves substituted for them.
- `e a : E a ⟶ K a.castSucc` is the requested surjection onto `K_a`.
  The `epi_g` component of `(ShortComplex.mk (i a) (e a) (w a)).ShortExact`
  asserts `Epi (e a)`.
- `i a : K a.succ ⟶ E a`, `w a : i a ≫ e a = 0`, and that same `ShortExact`
  assertion identify `K_{a+1}` as the kernel with its inclusion. In an abelian
  category `ShortComplex.ShortExact.fIsKernel` is the actual universal-property
  witness `IsLimit (KernelFork.ofι (i a) (w a))`. This is categorical kernel data,
  not just an arbitrary monomorphism or an isomorphic object with no specified map.
- The requested exact sequence `0 → K_r → E_{r-1} → ... → E_0 → F → 0` is
  encoded by its constituent short exact sequences. Its interior arrows are
  `e (a+1) ≫ i a`; they are determined by the displayed maps. At each `E_a`,
  the incoming image is the image of `i a`, since the preceding `e (a+1)` is
  epi; this is the kernel of `e a`. Postcomposing `e a` with the next mono
  does not change its kernel. At the left end `i (r-1)` is mono, and at the
  right end `e 0` is epi, with `K 0 = F`. Conversely the node's kernel-defined
  iterative construction supplies exactly these short exact sequences. Thus
  the finite-tower form keeps all endpoint and interior exactness clauses.
- `∀ a : Fin (r + 1), IsConstructibleEtaleModuleSheaf (K a)` asserts
  constructibility of every syzygy, including the starting and last terms.

Dependency declarations read and used:

- `def-weil-pbc-scheme-conventions` is a convention node with no declaration:
  its existing record explicitly collects the Mathlib properties. Scheme,
  compactness, quasi-separatedness, affineness and the etale site use their
  existing Mathlib/upstream encodings.
- `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`:
  `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf`, as currently
  recorded after Q142's repair. No second constructibility definition is made.
- `Sheaf.AlgebraicGeometry.ConstructibleModuleFiniteZeroCokernel`:
  `AlgebraicGeometry.Scheme.exists_affine_free_etale_zero_cokernel` supplies
  the iterative finite affine free surjection in the proof plan.
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves`: the mixed dependency record
  explicitly permits `CategoryTheory.Sheaf` with `ModuleCat` coefficients here.
  Its source was read through `scompile.py --source` because the older checkout
  lacks this file. The unrelated set-valued definitions are not copied.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`:
  `AlgebraicGeometry.Etale.etaleLowerShriek`, with the full coefficient-category
  assumptions and etale-map argument read in its source.
- Proof-only imports are the recorded
  `WeilConjectures.AlgebraicGeometry.FreeEtaleModuleShriekComparison`
  (`AlgebraicGeometry.Scheme.free_etale_module_shriek_comparison`, read via
  `scompile.py --source`),
  `Sheaf.AlgebraicGeometry.EtaleLowerShriekConstantConstructible`
  (`AlgebraicGeometry.Scheme.isConstructibleEtaleModuleSheaf_etaleLowerShriek_constant`),
  and `WeilConjectures.ConstructibleSheaf.KernelCokernel`
  (`AlgebraicGeometry.Scheme.IsConstructibleSheaf.kernel` and `.cokernel`).
  The module docstring includes both proof steps from the DAG and the finite-sum
  constructibility argument. The project comparison between the two
  constructibility interfaces is available through the imported dependency modules.
- `Mathlib.Algebra.Homology.ShortComplex.ShortExact`:
  `CategoryTheory.ShortComplex.ShortExact`; its source definition and its
  `fIsKernel` universal-property interface were checked.

Edge cases checked before writing: `r = 1` gives just one short exact sequence,
including a mono on the left and epi onto `F`. Each `n a` may be zero, so the
empty direct sum is allowed. For `F = 0` every family and every syzygy may be
zero; no positive-rank or nonempty-family condition is present. The empty
scheme and the zero coefficient ring are also allowed, with their zero sheaf
categories. No Noetherian, separation, invertibility, stalk bound, projectivity,
or nonzero condition is added. There is no requirement that a chosen free
cover split. The site/coefficient universes match the recorded dependencies;
finite indexing lies in `Type`, with no extraneous independent index universe.

Searches made for existing statements (all through the prescribed `msearch.py`
wrapper unless a direct source grep is named):

- LeanFinder: "A constructible etale module sheaf on a qcqs scheme admits
  arbitrarily long exact resolutions by finite sums of extensions by zero of
  constant rank one modules on affine etale objects". Eight hits: generic
  finite-presentation, module-category and condensed-module declarations; none
  states this finite affine etale syzygy theorem.
- Loogle: `CategoryTheory.ShortComplex.ShortExact, CategoryTheory.Limits.kernel`.
  Zero hits; the short-exact API was then inspected directly in Mathlib's source.
- Mathlib grep: `constructible.*syzyg|affine.*syzyg|constructible.*resolution`.
  Zero hits.
- LeanSearch: "Constructible etale sheaves have arbitrary finite resolutions by
  finite sums of extensions by zero of constant rank one module sheaves from
  affine etale objects". Eight generic finite-limit, finite-presentation,
  etale-topology and constant-sheaf hits, no matching theorem.
- Direct `rg` of `WeilConjectures/`, `lean/Sheaf/AlgebraicGeometry` and
  `dag/lean_names_upstream.json` for syzygy, finite-affine and constructible
  resolution patterns found unrelated Koszul/projective/cohomological material,
  not this statement. The exact item-id grep in upstream found no occurrence,
  and the proposed declaration name occurs in neither library nor name index.

Sources were read locally in `literature/stacks-project/etale-cohomology.tex`:
095N at `lemma-category-constructible-modules` explicitly gives affine objects
and the finite surjection in its proof; 03RZ at `lemma-constructible-abelian`
gives kernel and extension closure; 03S8 at `lemma-jshriek-constructible` gives
constructibility of the summands. There is no statement dispute or node fault.

## Second reading by Q42

I reread the node and the completed signature in a separate pass, matching
all hypotheses and conclusion clauses as above. The indexing uses `a.castSucc`
for `K_a` and `a.succ` for `K_{a+1}`, so there are exactly `r` covers and `r+1`
syzygies, and the final kernel is included in constructibility. The potentially
important mismatch checked was whether short-exactness merely asserts an
unidentified kernel: `ShortExact.fIsKernel` supplies its universal property for
the specified inclusion, and splicing supplies precisely the claimed long
exact sequence. No signature correction was needed. The finite-sum equality
uses `j_!` of the constant rank-one sheaf itself. All theorem proofs remain
`sorry` and all variables/universes are explicit. This is a worker self-check;
the maintainer's independent delivery review is still required. No other
agent was started, as instructed by the dispatcher.

## Second reading by Q119

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
