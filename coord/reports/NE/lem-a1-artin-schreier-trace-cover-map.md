## Worker report

The module `Sheaf.AlgebraicGeometry.ArtinSchreierTraceCoverMap` states all five clauses of
`lem-a1-artin-schreier-trace-cover-map`, with the original natural statement and dependency
lists unchanged. Its only postponed proof is
`AlgebraicGeometry.artinSchreier_trace_cover_map`. Every other declaration has real data.

The helper definitions are parts of this node's canonical construction, permitted by the
human's missing-helper authorization. They do not introduce independent mathematical notions:
`artinSchreierFunctionCover`, its projection and tautological root are the specified covers;
`artinSchreierBaseConstants` is the existing structural ring map;
`artinSchreierTracePolynomial` is the displayed finite sum; `artinSchreierFibreMap` is
Mathlib's pullback map; `ArtinSchreierTraceMaps` packages precisely the translations and trace
morphism with their coordinate and over-base equations. All are listed in `lean.declarations`.

Hypotheses, objects, and each clause:

| Natural statement | Lean rendering |
| --- | --- |
| Prime p | `(p : ℕ) [Fact p.Prime]` |
| q=p^r, r≥1 | `p ^ r`, `(hr : 1 ≤ r)` |
| k0=Fq, prime subfield Fp | `(k : Type u) [Field k] [Fintype k] [CharP k p]`, `hcard : Fintype.card k = p ^ r`, `[Algebra (ZMod p) k]`; the last structure is unique and is the prime-field embedding |
| Field trace | `Algebra.trace (ZMod p) k`, the actual multiplication trace, not a chosen functional |
| b in k0× | `(b : k) (hb : b ≠ 0)` |
| X a k0-scheme | `(X : Scheme.{u}) [X.Over (Spec (.of k))]` |
| X separated and finite type | `[IsSeparated (X ↘ Spec (.of k))]`, `[LocallyOfFiniteType (X ↘ Spec (.of k))]`, `[QuasiCompact (X ↘ Spec (.of k))]`; these last two are exactly finite type |
| Global function f | `(f : Γ(X, ⊤))` |
| Yq, Yp,b, structural maps, y and t | `artinSchreierFunctionCover X (p ^ r) f` and `artinSchreierFunctionCover X p (artinSchreierBaseConstants k X b * f)`, with the corresponding `Projection` and `Root` |
| Translations σc, τd | `M.σ c`, `M.τ d`, isomorphisms over X with `σ_root` and `τ_root` specifying pullback of the coordinate as y+c or t+d; `σ_zero`, `σ_add`, `τ_zero`, `τ_add` specify their additive actions |
| 1: πq finite étale | `IsFinite ... ∧ Etale ...` |
| 1: simply transitive on every geometric fibre | For every algebraically closed field Ω and every `x : Spec (.of Ω) ⟶ X`, the actual scheme `pullback πq x` is nonempty, and for any two of its underlying points `z z'`, `∃! c : k` sending z to z' by the pullback of `M.σ c` |
| 1: geometric fibre has q points | `Nat.card ↥(pullback πq x : Scheme.{u}) = p ^ r` |
| 2: Θb polynomial | `artinSchreierTracePolynomial p r b = ∑ i ∈ Finset.range r, (Polynomial.C b * Polynomial.X) ^ (p ^ i)` |
| 2: identity in OX[y] | For every `U : X.Opens`, `Θ^p-Θ = C bU * (X^(p^r)-X)` in `Polynomial Γ(X,U)`; constants and f are restricted using `X.presheaf.map` |
| 2: identity in the polynomial quotient | The next conjunct uses `AdjoinRoot.mk (X^(p^r)-X-C fU)` to assert `Θ^p-Θ = AdjoinRoot.of ... (bU*fU)`, again for every open U |
| 2: the induced X-morphism θb | `M.θ`, `M.θ_over`, `M.θ_root`; the last says exactly that pullback of t is the evaluation of Θb at the tautological y, with coefficients pulled back from X |
| 3: θb∘σc=τTr(bc)∘θb | `∀ c, (M.σ c).hom ≫ M.θ = M.θ ≫ (M.τ (Algebra.trace (ZMod p) k (b*c))).hom`; Lean composition is written in diagram order |
| 4: geometric surjectivity | `Function.Surjective (artinSchreierFibreMap _ _ x M.θ M.θ_over)` on the actual underlying points of the fibre schemes |
| 4: each fibre is a kernel orbit | Equality of the two images of `z z'` is equivalent to existence of `c : k` with `Algebra.trace ... (b*c)=0` and the fibre translation by c carrying z to z' |
| 4: kernel order q/p | `Nat.card {c : k // Algebra.trace (ZMod p) k (b*c)=0} = p ^ r / p` |
| 5: every h between separated finite-type k0-schemes | The final universal quantifier repeats the X' assumptions, binds `(h : X' ⟶ X) [h.IsOver (Spec (.of k))]`, and uses `h.appTop f` as f' |
| 5: canonical isomorphisms of covers | The witnesses `uq` and `up` preserve the tautological root and fit into `IsPullback` squares over h. Their induced isomorphisms to `pullback π h` are exactly the canonical comparisons. The root and structural-map equations specify the comparisons uniquely |
| 5: σ, τ and θ base change | `∀ c, (M'.σ c).hom ≫ uq = uq ≫ (M.σ c).hom`, the analogous equation for τ and up, and `M'.θ ≫ up = uq ≫ M.θ` |

Why the cover construction is the same relative Spec: it is the pullback of
`AffineSpace.artinSchreierMap PUnit X n` along
`AffineSpace.homOfVector (𝟙 X) (fun _ ↦ f)`. On an affine chart Spec A, this is the spectrum
of A[y]/(y^n-y-f), with projection the coefficient inclusion and `Root` the class of y.
These chart presentations commute with restrictions and give exactly the relative spectrum
in the node. This uses the existing relative-Spec interface; it does not replace a canonical
construction by an arbitrary scheme. Morphisms over X are determined by the pullback of y:
apply the pullback universal property and upstream `AffineSpace.hom_ext`.
Consequently `ArtinSchreierTraceMaps` specifies unique canonical maps, and the existential
conclusion asserts their existence with the stated properties rather than assuming it.
Likewise the coordinate-preserving comparison squares are equivalent to the node's
canonical isomorphisms, not isomorphisms left unspecified up to automorphism.

Dependency declarations read and used:

- `def-weil-pbc-scheme-conventions` is a convention record, explicitly without its own
  declaration. The theorem uses the recorded Mathlib meanings of schemes, separated and
  finite-type morphisms, geometric points and geometric fibre products.
- `def-fd-additive-character`: read `AddChar.FiniteField.primitiveChar` in
  `Mathlib.NumberTheory.LegendreSymbol.AddCharacter`, including its trace construction.
  No character is an additional hypothesis of this node. Its field-trace ingredient is
  `Algebra.trace` from Mathlib, as in that implementation.
- `def-weil-finite-integral-morphism`: `AlgebraicGeometry.IsFinite` in
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`; its affine-local finite ring-map condition
  is the one used in clause 1. The integral variant is not needed here.
- `def-weil-etale-morphism`: `AlgebraicGeometry.Etale` in
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`, the recorded affine-local ring-etale condition.
- `lem-weil-pbc-affine-morphism-relative-spec`:
  `AlgebraicGeometry.affine_morphism_relative_spec` in
  `WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec`; read the current full
  signature and docstring with `scompile.py --source`, since the older source checkout
  lacks this module. It supplies the equivalence and chart interpretation above.

All available modules of proof dependencies are imported. Mathlib leaves are supplied by
`Mathlib.RingTheory.AdjoinRoot`, `Mathlib.RingTheory.Etale.StandardEtale`,
`Mathlib.FieldTheory.Separable`, `Mathlib.FieldTheory.Finite.Trace` and the finite-field
basic module reexported by the upstream Artin–Schreier module. The named project proof
interfaces imported are `relative_spec_base_change`, the coherent/finite-type module,
`Scheme.Modules.exists_tensorPullback_affine_sections`, and `iterateFrobeniusOfPrime`.
The theorem docstring carries all nine steps of the node's natural-language proof, including
all named dependencies and the argument that does not assume Tr(1)≠0.

Edge cases checked before and during drafting:

- r=1: Θb=by, the map is the scaling isomorphism of prime-degree covers; the trace kernel
  is {0} and has size q/p=1. No r>1 assumption is imposed.
- p=2, r=2, b=1: Tr(1)=0 but Tr(α)=1 for α²+α+1=0 in F4. The kernel has size 2 and
  equivariance/surjectivity remain true. No invalid Tr(1) hypothesis occurs.
- f=0: both covers are split torsors. The theorem asserts the specified translation action,
  not that it exhausts the full automorphism group of a disconnected cover.
- X empty and empty opens: the cover pullback is empty and there are no geometric points
  over X; its section ring and polynomial identities are still defined for the zero ring.
  No `Nontrivial Γ(X,U)` hypothesis is present.
- Disconnected X, arbitrary b≠0, and arbitrary geometric points are included. The nonempty
  fibre clause is inside the geometric-point quantifier, so it does not require X nonempty.
- Identity h and the morphism from the empty scheme satisfy the same canonical comparison
  equations. No flatness or surjectivity assumption on h is added.

Searches made:

- `msearch.py ... leanfinder "The finite field trace polynomial gives a morphism of Artin
  Schreier covers equivariant under trace of translations"`: eight hits including
  `FiniteField.algebraMap_trace_eq_sum_pow`, Frobenius maps and extension lemmas; none
  states the five-clause scheme theorem.
- `msearch.py ... loogle "Algebra.trace, FiniteField.algebraMap_trace_eq_sum_pow"`:
  one hit, `FiniteField.algebraMap_trace_eq_sum_pow`. Its signature/docstring were opened;
  this is precisely a proof leaf and does not include the cover morphism.
- `msearch.py ... leansearch "Artin Schreier trace polynomial equivariant base change of
  covers"`: trace-equivalence and linear-map base-change lemmas, no matching statement.
- `msearch.py ... grep "artinSchreier|Artin.Schreier"`: only the KummerExtension file's
  introductory mention of Artin–Schreier theory in Mathlib, no cover construction.
- `rg -n 'artinSchreier|Artin.Schreier|ArtinSchreier'` in the project sources and
  `lean/Sheaf`: found the upstream affine-space Artin–Schreier module and Fourier-transform
  module. Read the former in full and reused its actual `artinSchreierMap`. Read the
  relevant affine-space coordinate, homOfVector, hom_ext and translation definitions.
  The side Artin–Schreier exact-sequence modules have a private existence lemma constructing
  a prime-degree cover by the same pullback; there is no reusable public cover declaration.
- `grep -rn 'lem-a1-artin-schreier-trace-cover-map'` in the upstream sources: no hits.
- Search for every newly introduced helper name in Mathlib, upstream, and `lean/Sheaf`:
  no collisions. `dag/lean_names_upstream.json` and the Artin–Schreier nodes were checked;
  `lem-fd-as-cover` supplies a different prime-degree assertion, not this statement.
- `tools/blueprint_refs.py ancestor` identifies `lem-a1-unramified-nonexceptional`.
  Opened its current main-20261015 proof, case a≠0, and the local Laumon PDF at (1.1.3),
  pp. 139–140: the context is Lang torsors and their pushouts, exactly as the node's
  source/proof-origin records state. The explicit trace calculation is the DAG's expansion.

Validation: the prescribed `scompile.py NE lem-a1-artin-schreier-trace-cover-map` compiled
this single module both as a sandbox file and under its real module name, with no errors
and no warnings. No direct compilation, global build, or shared-repository edits were used.
No statement correction, disputed statement, dependency repair, or new definition node
was needed.

## Second reading by NE

Author's second pass, with the original node and final module open; the maintainer provides
the independent review. I checked each row above against both texts. The main risks were
silently replacing geometric fibre-scheme points by Ω-valued lifts, omitting either the
polynomial or quotient identity, leaving canonical comparison maps arbitrary, and losing
the action laws in the translation package. The final file uses explicit scheme-sort
coercions for every fibre cardinal and point binder, includes both identities on every open,
specifies comparisons by their root pullback and cartesian square, and includes all four
zero/addition equations for the translation actions. Coordinate formulas and over-X
conditions characterize every packaged map uniquely. The commutative squares have the
correct diagram-order composition. All finite-type hypotheses, all geometric-point
quantifiers, the trace kernel size and the arbitrary-base-change clause are present.
No mathematical mismatch or node change was found.
