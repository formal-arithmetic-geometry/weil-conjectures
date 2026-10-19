## Worker report

Item: `lem-sf-tensor-ctf`. The module `Sheaf.Paper.FiniteCoefficientTensorCtf`
states `AlgebraicGeometry.Scheme.finiteCoefficient_tensor_ctf`, with one `sorry`
and no new definitions or proved lemmas. The node's mathematical statement is unchanged.
Four already recorded definition nodes were added to `stmt_deps` to expose the
finite-field datum, derived tensor, intrinsic constructibility and interval predicates
actually used by the signature. No new nodes or dependency modules are needed.

### Hypothesis and conclusion correspondence

- The global finite-field datum is `D : WeilConjectures.FiniteFieldDatum.{u}`.
  Its fields supply `p`, the finite base field, and the fixed algebraic closure `D.k`.
- The prime is `(l : ℕ) [Fact l.Prime]`, and the distinctness is `_hl : l ≠ D.p`.
- A finite extension of `ℚ_l` is `(E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]`. The quotient `A_{E,n}` is exactly the
  existing `Padic.coefficientExtensionRing l E n`, with its existing chosen uniformizer.
- Positive exponent is `(n : ℕ) (hn : 1 ≤ n)`; level zero is not admitted.
- A finite-type `k`-scheme is `(X : Scheme.{u}) [X.Over (Spec (CommRingCat.of D.k))]`
  together with `LocallyOfFiniteType` and `QuasiCompact` on its structure morphism.
  There is no separatedness, properness, smoothness or nonemptiness assumption.
- The derived inputs are `DerivedCategory.Q.obj K` and `DerivedCategory.Q.obj M`
  for arbitrary cochain representatives in the recorded constant-coefficient
  module-sheaf category on `X.ProEt`.
- `_hK : WeilConjectures.finiteTorConstructible ... (DerivedCategory.Q.obj K)`
  renders membership in `Dᵇ_ctf(X,A)`. `_hKa : HasProEtaleTorAmplitude ... a b`
  renders its specified interval. The latter predicate includes `a ≤ b`.
- `_hM : intrinsicFiniteTorsionConstructible ... (DerivedCategory.Q.obj M)`
  renders bounded constructibility of the second input. This is precisely finite
  cohomological support and constructibility of every cohomology sheaf, not an
  independently assumed etale-origin condition.
- `(P, f : P ⟶ K, hf : QuasiIso f, hP : CochainComplex.IsKFlat ... P)` specifies
  any resolution used by the existing `derivedTensor`. This is its recorded
  representative interface, also used by `finiteTensor_constructible_cohomology`.
  No bound, termwise constructibility, or termwise flatness is imposed on this
  arbitrarily chosen resolution. Every derived input has a cochain representative
  and a K-flat resolution; universally quantifying them is the representation of
  the canonical derived tensor, not an additional mathematical restriction.
- Clause (i) is the first conjunct, `intrinsicFiniteTorsionConstructible ...
  (derivedTensor X ... K M P f hf hP)`.
- Clause (ii) is `∀ c d : ℤ`, followed by the additional premise
  `WeilConjectures.finiteTorConstructible ... (DerivedCategory.Q.obj M)` and
  `HasProEtaleTorAmplitude ... (DerivedCategory.Q.obj M) c d`.
  Its conclusion contains both `WeilConjectures.finiteTorConstructible` of the
  same tensor and `HasProEtaleTorAmplitude` of that tensor in `(a + c) (b + d)`.
  Thus neither finite-Tor membership nor the specified sum interval is omitted.

### Dependencies read and used

- `Sheaf.Paper.FiniteTorAmplitude`: `WeilConjectures.finiteTorConstructible`
  and its full-subcategory interpretation. The current server source was read
  with `scompile.py --source`; it agrees with the shared copy. This definition
  is intrinsic bounded constructibility intersected with finite Tor amplitude.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible`.
- `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude`:
  `AlgebraicGeometry.Scheme.HasProEtaleTorAmplitude` and
  `HasFiniteProEtaleTorAmplitude`. The former tests every degree-zero module
  against every K-flat resolution of a representative of the input.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`:
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`. It is the derived category
  of modules over the constant CommRingCat sheaf after forgetting to RingCat;
  coefficients and modules are lifted to size `u+1` while the small pro-etale
  site retains objects at `u+1` and morphisms at `u`.
- `Sheaf.Algebra.Homology.DerivedTensor`:
  `AlgebraicGeometry.Scheme.derivedTensor`, using the total complex of the
  recorded sheaf tensor and an arbitrary K-flat resolution of its first factor.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor`, the `mathlib_match` of
  `def-weil-derived-cohomology-sheaves`, used inside the recorded predicates.
  Its full signature and factorization docstring were read.
- `def-weil-scheme-morphism-properties` is a convention node with no declaration.
  Its finite-type clause is rendered by Mathlib's `LocallyOfFiniteType` and
  `QuasiCompact`, whose definitions were read, and its scheme-over-base convention
  is Mathlib's `Scheme.Over` structure morphism.
- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`; the coefficient
  extension ring is imported from `Sheaf.NumberTheory.Padics.CoefficientExtension`.

The proof plan in the declaration docstring follows all four DAG proof steps:
choose the first bounded flat model, perform the two good truncations of the second
input to bound the totalization, apply constructible-cohomology preservation, and
use the second flat model and finite-sum flatness to obtain the sum Tor interval.
The available proof-dependency modules are imported without `public`.

One proof-only upstream import was omitted after an actual compiler collision:
`WeilConjectures.SixFunctors.ProEtale.Derived.Tensor` imports the older
`ProEtale.UpperLowerStar.Defs`, which redeclares
`AlgebraicGeometry.ProEtale.«term(_)_*[_]»` already imported by the recorded
finite-Tor definition through the reorganized `FiniteCoefficient.UpperLowerStar.Defs`.
The compiler reported this on both the local and server paths. The exact recorded
functoriality declaration is in `...Derived.TensorResolution`, whose current server
source was also read: it imports that same conflicting `...Derived.Tensor`.
Its proof record has no `lean.module`. The statement uses only the compatible
recorded `Scheme.derivedTensor`; this omission does not replace any statement notion.
The name of the functoriality node remains in the proof docstring and DAG proof plan.
Stage 3 will need the corresponding functoriality/representative transport in this
module-sheaf encoding; the upstream sheaf-valued declaration is not silently identified
with it.

### Edge cases

The empty scheme and zero inputs are allowed. No inhabitedness or nonzero-sheaf
hypothesis occurs. The zero complex remains constructible and has Tor amplitude
in any ordered interval. Singleton intervals (`a = b` and `c = d`) are allowed;
negative endpoints and all integer shifts are allowed. No artificial strict
inequality between the original amplitude endpoints is added. If an interval
were reversed, `HasProEtaleTorAmplitude` itself fails its order conjunct, exactly
as the dependency defines it. Exponent `n = 1` is covered. Only one factor has to
be finite Tor for clause (i); there is no premature finite-Tor premise on `M`.
There is no equality imposed between the site's object and morphism universes.
The single common universe follows the existing recorded finite-coefficient
category and includes the project's size convention.

### Searches for existing declarations

Searches were run on 2026-10-16 through the prescribed `msearch.py` wrapper and
with `rg` over Mathlib, the source project, the shared project modules and the
upstream name index.

- LeanFinder: `derived tensor product preserves bounded constructible complexes and
  adds finite Tor amplitude intervals` returned Tor functors, tensor infrastructure,
  and derived-category cohomological bounds, with no constructible pro-etale theorem.
- Loogle: `HomologicalComplex.tensorObj` returned the ordinary tensor complex and its
  unitors/associators/summand maps, not the required derived constructibility statement.
- Mathlib grep: `torAmplitudeIn|finiteTorConstructible|constructible.*tensor` in
  `CategoryTheory` returned no hits.
- LeanSearch: `Derived tensor of bounded constructible pro etale sheaf complexes
  preserves finite Tor amplitude with sum interval` was unavailable (Internal Server
  Error), which the wrapper recorded as unavailable.
- Project grep: `lem-sf-tensor-ctf|boundedConstructible_tensor|
  constructibleFiniteTor_tensor|torAmplitudeIn_tensor` found the etale upstream
  analogues in `SixFunctors/Etale/Derived/Stability/{Basic,OpenImmersion}.lean`.
  Their full signatures and docstrings were read. These concern
  `Sheaf X.smallEtaleTopology (ModuleCat Λ)` and the upstream etale constructibility
  predicate, and therefore are not the pro-etale module-sheaf statement of this item.
  The generic `DerivedCategory.torAmplitudeIn_tensor` supplies only the interval
  assertion in another interface, not either constructibility conclusion here.
- Project grep for `finiteTorConstructible|intrinsicFiniteTorsionConstructible`
  located the exact dependency definitions and related flat-model/cohomology statements.
  No pro-etale tensor-ctf preservation theorem was found in this recorded encoding.
- The proposed full declaration name `finiteCoefficient_tensor_ctf` has no hit in
  `dag/lean_names_upstream.json`, Mathlib, upstream `WeilConjectures`, or shared
  `lean/Sheaf`. A grep of the blueprint id in upstream sources finds only the
  etale analogues described above.

### Validation

`scompile.py Q22 lem-sf-tensor-ctf` compiled the module cleanly after the import
collision was removed: sandbox check 11.2 seconds and actual module 9.4 seconds,
each within the unmodified 60-second limit. No global build or direct compiler
invocation was used. All binders and the universe are explicit; `autoImplicit false`
is set. The signature in `lean.statement` is copied verbatim through the text before
`:=`. The final packaging dry run is required before READY.

No mathematical statement correction, new definition node, or disputed assertion.
The local reference checkout lacks the blueprint markdown path recorded in the DAG;
the current node's full statement and four detailed proof paragraphs were read directly.

## Second reading by Q22

I independently read the base DAG node, the sandbox node and module, and the
blueprint source at
`/home/ubuntu/weil-launcher-nt/literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/lem-sf-tensor-ctf.md`.
This corrects the worker report's final source-availability note: the source is
available on this machine outside the shared checkout. Its statement agrees
verbatim with the DAG statement. I also read the enclosing unit's `_section.md`
and the global datum and finite-torsion constructibility source nodes. The unit's
separatedness assumption is on the biduality proposition; this tensor lemma itself
explicitly allows any finite-type k-scheme, as its Lean does. For the interval
notion I read Stacks `sites-cohomology.tex`, label `definition-tor-amplitude`, in
that same literature tree: a ringed site, an arbitrary derived object, ordered
integer endpoints, and all module sheaves in degree zero are exactly its inputs.

Object, hypothesis and conclusion checklist, in source order:

1. Global datum `(p,a,q,k₀,k)`: `D : WeilConjectures.FiniteFieldDatum.{u}`.
   I opened `Sheaf.Paper.FiniteFieldFiber`: primality, positive field exponent,
   cardinality q = p^a, finite base field and fixed algebraic closure are its
   actual fields. Verdict: exact. No descent datum for X is assumed by this lemma.
2. Prime l distinct from p: `(l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)`.
   Verdict: exact; characteristic p follows from the finite-field datum, rather
   than being an unrelated extra characteristic instance.
3. Finite extension E/Q_l and A = A_{E,n}: `(E : Type u) [Field E]
   [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`, with the recorded
   `Padic.coefficientExtensionRing l E n` throughout. I opened
   `CoefficientExtension.lean`: it is the quotient of the recorded integer ring
   by `(Ideal.span {coefficientExtensionUniformizer l E}) ^ n`. Verdict: exact;
   neither a field coefficient replacement nor an arbitrary finite ring is used.
4. Positive level n: `(n : ℕ) (hn : 1 ≤ n)`. Verdict: exact.
5. Finite-type k-scheme X: `(X : Scheme.{u})
   [X.Over (Spec (CommRingCat.of D.k))]` and `LocallyOfFiniteType` plus
   `QuasiCompact` of its structure morphism. I read Mathlib's `FiniteType.lean`
   definition and the convention dependency. Verdict: exactly finite type;
   no properness, separatedness, smoothness or inhabitedness premise.
6. K and M in D(X_proet,A): `DerivedCategory.Q.obj K` and
   `DerivedCategory.Q.obj M`, for arbitrary cochain representatives in
   `proEtaleRingModules X (proEtaleConstantRing X A)`. I opened the recorded
   `ProEtaleDerivedCategory`, `ProEtaleOperations` and `RingedSiteModules`
   declarations. They give the same `SheafOfModules` category over the constant
   commutative ring sheaf, forgotten to RingCat, with standard localization.
   Verdict: exact; the category is neither an etale category nor a completed one.
7. K in Dᵇ_ctf with interval [a,b]: `_hK : finiteTorConstructible ... (Q.obj K)`
   and `_hKa : HasProEtaleTorAmplitude ... (Q.obj K) a b`, with `(a b : ℤ)`.
   I opened `FiniteTorAmplitude.lean`: the first predicate is precisely intrinsic
   bounded constructibility intersected with existence of a finite Tor interval.
   I opened `ProEtaleTorAmplitude.lean`: the second includes a ≤ b and tests all
   degree-zero modules on every K-flat representative resolution. Verdict: exact.
8. M in Dᵇ_c: `_hM : intrinsicFiniteTorsionConstructible ... (Q.obj M)`.
   I opened its definition and `ProEtaleConstructibleSheaf.lean`: finite support
   of cohomology, with a finite locally closed constructible partition and locally
   constant finite stalks for every cohomology sheaf. I read Mathlib's
   `DerivedCategory.homologyFunctor` and `homologyFunctorFactors` signatures.
   Verdict: exact; no Tor hypothesis on M is present in clause (i).
9. The derived tensor: `derivedTensor X A K M P f hf hP`.
   I opened `DerivedTensor.lean` and the two-universe `CochainComplex.IsKFlat`
   definition. `(P, f : P ⟶ K, hf : QuasiIso f, hP : IsKFlat P)` specifies any
   K-flat resolution computing the tensor totalization. These are computation
   data, not a bounded/flat/constructible model hypothesis on the inputs.
   Universally quantifying them covers every such computation. Verdict: exact.
10. Conclusion (i): the first conjunct is
    `intrinsicFiniteTorsionConstructible ... (derivedTensor ...)`.
    Verdict: exactly Dᵇ_c membership of the specified tensor.
11. Conditional conclusion (ii): `∀ c d : ℤ`, followed by membership
    `finiteTorConstructible ... (Q.obj M)` and
    `HasProEtaleTorAmplitude ... (Q.obj M) c d`, implies the conjunction of
    `finiteTorConstructible ... (derivedTensor ...)` and
    `HasProEtaleTorAmplitude ... (derivedTensor ...) (a + c) (b + d)`.
    Verdict: both clauses are present, in the stated conditional scope, with the
    same tensor and the correct endpoint sums. The premise on M has not been
    moved into clause (i).

Edge cases: zero complexes, the empty scheme and empty cohomological support are
allowed. A constructibility witness may use one empty stratum on the empty
scheme; the dependency's positive number of strata does not exclude it. There
is no free index set in this theorem. Level n = 1 is included; n = 0 is excluded
by the source itself. Singleton ordered intervals and all negative endpoints
are included. Reversed intervals fail the dependency's explicit order conjunct,
consistent with Stacks 08FZ. All primes distinct from p are allowed. Site objects
remain in universe u+1, morphisms in u, and coefficients/modules in u+1 via the
recorded lift; `IsKFlat.{u+1,u}` preserves this distinction. The common ambient
universe for the scheme, finite extension and datum is the recorded size
convention and may be enlarged; no equality of site universes is added.

Independent searches (2026-10-16):

- LeanFinder through `msearch.py`: `bounded constructible complexes tensor closure
  finite Tor dimension sheaves on a site`. Hits were generic `CategoryTheory.Tor`
  and derived-category cohomological support lemmas, with no matching theorem.
- Loogle through `msearch.py`: `CochainComplex.IsKFlat` is unknown to that index;
  I do not count its zero hits as evidence of absence. A valid follow-up query
  `CategoryTheory.Tor` returned the generic Tor bifunctor, its object/map formulas
  and higher-Tor vanishing for projective objects, with no constructibility result.
- LeanSearch through `msearch.py`: `constructible sheaves derived tensor product
  bounded finite Tor dimension` was unavailable (Internal Server Error).
- Independent `rg` in Mathlib homological algebra, upstream SixFunctors, shared
  `lean/Sheaf`, and the upstream name index, using
  `tensor.*[Cc]onstructible|[Cc]onstructible.*tensor|torAmplitude.*tensor` and the
  proposed declaration/id, found the upstream etale tensor stability theorems
  and the existing pro-etale constructible-cohomology dependency. I opened
  `Etale/Derived/Stability/Basic.lean` and `OpenImmersion.lean`: their signatures
  concern `Sheaf X.smallEtaleTopology (ModuleCat Λ)` with etale predicates.
  They do not state this node in its recorded pro-etale module category. The
  generic Tor interval theorem only proves the interval part. The existing
  `finiteTensor_constructible_cohomology` supplies no boundedness or finite-Tor
  conclusion. No exact existing declaration was found.

H4/H5/H6/H8/H9 audit: all eight statement dependency records were read against
these actual declarations (the morphism-properties node is a convention).
The four added statement dependencies are already landed definition nodes;
no new definition node or dependency module is delivered. There is no private
notion, hollow definition, theorem proof, local notation or unbound universe in
this module: its sole theorem has exactly one `sorry`. Its docstring carries the
source/id and all four DAG proof steps, including good truncation and the finite
sum flatness argument. Proof dependencies with recorded compatible modules are
imported. I also read `ProEtale/Derived/TensorResolution.lean`: its sheaf-valued
functoriality declaration imports the legacy `Derived.Tensor`/`UpperLowerStar.Defs`
chain, confirming the worker's documented import incompatibility. No upstream
sheaf-valued theorem is being treated as a module-sheaf statement here.

Mismatches and changes: no mathematical or Lean-signature mismatch was found.
The only correction is the source-availability documentation above; I leave the
correct module and node unchanged. The direct source reading and independent
checklist/search evidence are added in this section. No statement correction or
citer audit is required.

Validation: the prescribed `scompile.py Q22 lem-sf-tensor-ctf
lean/Sheaf/Paper/FiniteCoefficientTensorCtf.lean` passed with no errors or warnings:
sandbox 7.4 s, actual module 17.9 s, default 60-second limits. A literal comparison
confirmed `lean.statement` equals the complete file signature before `:=`;
all lines are at most 100 characters. Final delivery preflight follows.
