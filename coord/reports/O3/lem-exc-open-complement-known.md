## Worker report

The draft module `Sheaf.AlgebraicGeometry.OpenComplementKnown` states
`AlgebraicGeometry.Scheme.hasOpenComplementCondition_of_isAlgClosure_finite_and_lowDimension`.
It has one theorem with proof `sorry`, no definitions, no new nodes, and no changes to
other nodes. The item copy changes only `lean`. Compilation is currently prevented by
an unconditional compiler-overlay failure described below; this draft is not certified.

The source node and its fifteen proof steps were read in full. The main-20261015
blueprint moved this source to `sec-six-functors-basics/sk-prop-a1-kummer/`;
its general statement and independent low-dimensional assertions agree with the node.
The older source recorded by the node was also read. No statement correction is needed.
The proof docstring carries all fifteen steps, including the stage-1 repair replacing
unjustified arbitrary-etale finite-type assertions by affine-etale arguments and
sheafification on an affine cover.

Hypotheses and clauses:

| Node text | Lean rendering |
| --- | --- |
| Algebraic closure of a finite field | `(k : Type u) [Field k]` and `hk : ∃ k₀ : Subfield k, Finite k₀ ∧ IsAlgClosure k₀ k`; the subfield has its canonical algebra structure on k. |
| Nonnegative integer d | `(d : ℕ)`; no positivity is imposed. |
| T a k-scheme | `{T V : Scheme.{u}} [T.Over (Spec (.of k))]`. |
| T finite type | Both `[LocallyOfFiniteType (T ↘ Spec (.of k))]` and `[QuasiCompact (T ↘ Spec (.of k))]`, the dependency's recorded definition. |
| Dimension at most d | `hdim : topologicalKrullDim T ≤ (d : WithBot ℕ∞)`; this retains dimension minus infinity for the empty scheme. |
| Specified quasi-compact open immersion | `(j : V ⟶ T) [IsOpenImmersion j] [QuasiCompact j]`. |
| Finite commutative coefficient ring | `(A : Type (u + 1)) [CommRing A] [Finite A]`, the coefficient and sheaf universes of the recorded predicate. |
| Prime ell different from the characteristic | `(ℓ : ℕ) (hprime : ℓ.Prime) (hchar : ℓ ≠ ringChar k)`. |
| Power of ell annihilates A | `hkill : ∃ n : ℕ, (ℓ ^ n : ℕ) • (1 : A) = 0`; annihilating the unit is equivalent to annihilating every element. Exponent zero is allowed and forces the zero ring, consistent with the node's proof. |
| Open-complement condition at A with c=2d | First conjunct `HasOpenComplementCondition A j (2 * d)`, using the recorded definition without replacement. Its first clause quantifies over arbitrary module sheaves and all integer q>2d, and its second over constructible sheaves and every integer q. |
| Dimension-zero independent assertion | Conditional second conjunct with antecedent `topologicalKrullDim T ≤ 0`. |
| Such an open immersion is also closed | `IsClosedImmersion j`, using the recorded Mathlib declaration. No Noetherian hypothesis is added: finite type over k supplies it in the proof. |
| Its direct image is exact | `PreservesFiniteColimits (Etale.lowerStar (ModuleCat.{u + 1} A) j)`. The same canonical additive lower-star functor already preserves finite limits by `Etale.preservesFiniteLimits_lowerStar`, so this is precisely its additional right-exactness assertion. |
| Its direct image is extension by zero | `Nonempty (Etale.lowerStar (ModuleCat.{u + 1} A) j ≅ Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j)`; both functors are the existing canonical constructions, not arbitrary supplied functors or maps. |
| Preserves constructibility | For every module sheaf F, `IsConstructibleEtaleModuleSheaf F → IsConstructibleEtaleModuleSheaf ((Etale.lowerStar ... j).obj F)`. |
| The condition holds in dimension zero | `HasOpenComplementCondition A j 0`, independently proved in the docstring by the clopen decomposition. |
| Dimension-at-most-one vanishing and constructibility | Third conjunct `topologicalKrullDim T ≤ 1 → HasOpenComplementCondition A j 1`; by the predicate's actual body this explicitly includes vanishing for every integer q>1 and every module sheaf, and constructibility in all integer degrees. |

Independence is a requirement on the proof route, rather than an extra assumption in
the proposition: docstring Steps 13-14 use the clopen argument and Step 15 uses the two
recorded curve theorems, without using the general direct-image input.

Dependency declarations read and used:

| Node | Module | Declaration |
| --- | --- | --- |
| `def-weil-finite-type-morphism` | `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` | `AlgebraicGeometry.LocallyOfFiniteType` |
| `def-kun-topological-krull-dimension` | `Mathlib.Topology.KrullDimension` | `topologicalKrullDim` |
| `def-weil-open-immersion` | `Mathlib.AlgebraicGeometry.OpenImmersion` | `AlgebraicGeometry.IsOpenImmersion` |
| `def-exc-open-complement-bound` | `Sheaf.AlgebraicGeometry.OpenComplementCondition` | `AlgebraicGeometry.Scheme.HasOpenComplementCondition` |
| `thm-exc-curve-open-dimension-general` | `Sheaf.AlgebraicGeometry.CurveOpenDimensionGeneral` | `AlgebraicGeometry.Etale.isZero_higherDirectImage_of_open_curve` |
| `thm-exc-curve-open-constructible-general` | `Sheaf.AlgebraicGeometry.CurveOpenConstructibleGeneral` | `AlgebraicGeometry.Etale.isConstructibleEtaleModuleSheaf_higherDirectImage_of_open_curve` |
| `pqf-def-locnoeth` | `Mathlib.AlgebraicGeometry.Noetherian` | `AlgebraicGeometry.IsLocallyNoetherian` |
| `def-weil-closed-immersion` | `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` | `AlgebraicGeometry.IsClosedImmersion` |

The recorded `HasOpenComplementCondition` body was read, not merely its signature.
Both curve declarations' full signatures and proof docstrings were read. The independent
curve statements use the same sheaf and coefficient universes. The canonical direct
image and extension-by-zero definitions were read in
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` and
`WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`.
The additional module imports are the published modules of the stated proof dependencies.

Edge cases checked mathematically before drafting: empty T (hence empty V), empty V in
nonempty T, d=0, d=1, arbitrary d, the zero coefficient ring, annihilation exponent zero,
negative cohomological degrees, and nonconstructible input sheaves in the vanishing
clause. There are no nonempty, reduced, separated, connected, or positive-dimension
hypotheses. For dim T≤1 the bound one includes q=2; for dim T≤0 the bound zero also
includes q=1, which a mere use of the curve bound would miss.
No `let`, hidden `show ... from`, local notation, local instance, private notion,
auto-bound variable, or proof other than `sorry` occurs.

Searches made with the prescribed search wrapper:

- LeanFinder: “A quasi-compact open immersion into a finite type scheme over the algebraic closure of a finite field has constructible higher direct images and cohomological dimension at most twice the dimension”. Eight hits: quasi-compactness of open immersions into locally Noetherian schemes, quasi-compact Proj, compact fibres, local quasi-finiteness, constructible images, quasi-compactness from compactness, immersions locally quasi-finite, finite morphisms proper. None states the higher-direct-image assertions.
- Loogle: `HasOpenComplementCondition`. Zero hits (unknown identifier in Mathlib).
- LeanSearch: “Higher direct images of constructible etale sheaves along a quasi compact open immersion are constructible and vanish above twice the dimension of a finite type scheme over an algebraically closed field.” Eight hits, concerning constructible images and structure-sheaf restriction; none matches.
- Mathlib grep via msearch: `openComplement|HasOpenComplementCondition|higherDirectImage.*open`. Zero hits.
- Direct rg in upstream `WeilConjectures` and project `lean/Sheaf`: `lem-exc-open-complement-known|HasOpenComplementCondition|hasOpenComplementCondition`. Upstream has no match; project contains the predicate and the broader separately closed-base theorem in `Sheaf.Paper.OpenComplementUnconditional`, plus its finite-stage/chart variants and a chart hypothesis. That theorem has a more general field hypothesis and does not bundle the node's independent closed/exact/extension-by-zero and curve conclusions. It is therefore not an exact existing binding for this full node. No duplicate predicate is defined.
- `dag/lean_names_upstream.json`: `openComplement|OpenComplement|lem-exc-open-complement-known`; zero hits.
- The recorded Mathlib definitions were inspected directly in FiniteType, QuasiCompact, OpenImmersion, ClosedImmersion, Noetherian, and KrullDimension; the example CompactObject module and node record were read.

No STATEMENT-DISPUTED flag or node fault is asserted.

## Compiler and dry-run verification, 2026-10-16

The first prescribed `scompile.py` invocation exposed a stale local side-overlay file:
the forced `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs`
source imports the ordinary pro-etale definitions and redeclares
`AlgebraicGeometry.ProEt.overPullbackId` at line 119. The same duplicate was reported by
the server confirmation, before this module was elaborated. The current project source
contains the canonical declaration only in the ordinary published module; no project or
live source was edited.

For the authorized local side-overlay check, I copied the overlay into
`scratchpad/overlay-fixed` and removed only that stale duplicate declaration, leaving the
current module source and all published artifacts unchanged. With `NT_OVERLAY_SOURCE` set
to this sandbox copy, `scompile.py N3 lem-exc-open-complement-known
lean/Sheaf/AlgebraicGeometry/OpenComplementKnown.lean` compiled the overlay and this
module cleanly (sandbox and library passes; the one expected `sorry` warning is suppressed
by the project options). This confirms the item itself has no elaboration or import error.

The required dry run was then executed with the same sandbox-only overlay repair:
`NT_OVERLAY_SOURCE=$PWD/scratchpad/overlay-fixed python3
/home/ubuntu/weil-launcher-nt/deliver2.py N3 lem-exc-open-complement-known --no-push`.
It returned `OK (dry run): commit 36a4124950 compiles and passes the preflight except for
the second reading, which the second reader writes; nothing pushed.` The remote preflight
therefore passed. No live source, compiler, manifest, or library artifact was modified.

Static self-check: only the node's `lean` field differs from the repository node; the
recorded signature is verbatim from the module; every Lean line is at most 100 characters;
and the theorem's sole proof is the expected single `sorry`.

## Second reading by N3

I independently read the complete sandbox theorem and node (including all fifteen proof
steps), each of its eight statement-dependency nodes and their recorded declarations,
the original blueprint source and the main-20261015 statement and proof under
`sec-six-functors-basics/sk-prop-a1-kummer/`. The current source agrees with the node's
statement. The Stacks finite-type definition and affine characterization
(`morphisms.tex`, definition-finite-type and lemma-locally-finite-type-characterize,
Tags 01T0/01T2) impose no additional separatedness or nonemptiness assumption.
I also read `etale-cohomology.tex`, lemma-higher-direct-images (03Q8): the cohomology
presheaf is sheafified, as the theorem's proof docstring correctly says. No released
repair note exists for this item. There is no stage-2 statement correction to audit.

My object/hypothesis/conclusion checklist, with the Lean file open:

| Node item | Lean rendering and second-reader verdict |
| --- | --- |
| A field k which is an algebraic closure of a finite field | `(k : Type u) [Field k]` and `hk : ∃ k₀ : Subfield k, Finite k₀ ∧ IsAlgClosure k₀ k`. Exact: the actual finite subfield carries the canonical algebra structure; `IsAlgClosure` asserts algebraicity and algebraic closedness. This does not assume k itself finite. |
| A nonnegative integer d | `(d : ℕ)`. Exact; zero is included. |
| A k-scheme T | `{T V : Scheme.{u}} [T.Over (Spec (.of k))]`. Exact: T's structure map is `T ↘ Spec (.of k)`. V's map to the base is its composite with j and need not be separately supplied. |
| T is of finite type over k | `[LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]`. Exact conjunction specified by the dependency record and Stacks, with no additional geometric condition. I opened both Mathlib class bodies. |
| Krull dimension at most d | `hdim : topologicalKrullDim T ≤ (d : WithBot ℕ∞)`. Exact: the dependency's definition uses chains of irreducible closed sets and retains minus infinity for empty T. |
| Specified quasi-compact open immersion V into T | `(j : V ⟶ T) [IsOpenImmersion j] [QuasiCompact j]`. Exact: these are the recorded Mathlib notions, not an arbitrary map or a separately chosen open subset. |
| A finite commutative coefficient ring A | `(A : Type (u + 1)) [CommRing A] [Finite A]`. Exact, using the coefficient universe of the recorded predicate. No nontriviality assumption excludes the zero ring. |
| A prime ell different from the characteristic of k | `(ℓ : ℕ) (hprime : ℓ.Prime) (hchar : ℓ ≠ ringChar k)`. Exact; no unsupported invertibility assumption is added. Its image is a unit in k and hence in global sections of T, supplying the curve dependencies' invertibility hypothesis. |
| A is killed by a power of ell | `hkill : ∃ n : ℕ, (ℓ ^ n : ℕ) • (1 : A) = 0`. Exact: annihilating the unit annihilates every A-module element. If n is zero, A is the zero ring; a positive annihilating exponent can still be chosen. |
| General open-complement condition with c=2d | First conjunct `HasOpenComplementCondition A j (2 * d)`. Exact, using the dependency's definition unchanged. Its first conjunct quantifies over every module sheaf M and integer q greater than the bound and asserts `IsZero` of the homology sheaf of `Etale.rightDerivedLowerStarPlus` on M in degree zero. Its second quantifies over every constructible F and every integer q. |
| Independent dimension-zero assertion | Second conjunct has antecedent `topologicalKrullDim T ≤ 0`. Exact; no hypothesis that the supplied bound d itself equals zero is imposed. |
| In dimension zero, j is also closed | `IsClosedImmersion j`. Exact recorded Mathlib class, with closed embedding and surjectivity on stalks. No separate Noetherian hypothesis is assumed: finite type over k supplies Noetherianity. |
| Its direct image is exact | `PreservesFiniteColimits (Etale.lowerStar (ModuleCat.{u + 1} A) j)`. Exact: I opened the actual pushforward definition, its additive instance and `Etale.preservesFiniteLimits_lowerStar`; left exactness is already canonical, and this conjunct supplies right exactness. |
| Its direct image is extension by zero | `Nonempty (Etale.lowerStar (ModuleCat.{u + 1} A) j ≅ Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j)`. Exact existence of a natural isomorphism between the actual functors. I opened both definitions: lowerStar is pushforward along site base change, and lowerShriek is localization extension by zero with its restriction adjunction. No functor or map is an arbitrary input. |
| It preserves constructibility | `∀ F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A), IsConstructibleEtaleModuleSheaf F → IsConstructibleEtaleModuleSheaf ((Etale.lowerStar ... j).obj F)`. Exact; the constructibility predicate is the existing finite locally closed stratification/trivialization definition, which I opened. |
| Dimension-zero condition | `HasOpenComplementCondition A j 0`. Exact: includes vanishing in degree one, which the curve bound alone would not imply. |
| Independent dimension-at-most-one assertions | Third conjunct `topologicalKrullDim T ≤ 1 → HasOpenComplementCondition A j 1`. Exact: vanishing for every M and every integer q>1, plus constructibility in every integer degree. |

The quantifiers have the node's order: the geometric dimension bound is fixed before
A and ell, and the condition then quantifies over sheaves and integer degrees. The
low-dimensional clauses apply to the same T, j and A. The natural-language requirement
that these be proved independently is implemented in docstring Steps 13-15: clopen
product and exactness in dimension zero; the two curve results in dimension at most
one. Steps 1 and 15 together supply a positive annihilator when applying the curve
constructibility declaration, whose signature requires a positive exponent.

I opened the full signatures of `Etale.isZero_higherDirectImage_of_open_curve` and
`Etale.isConstructibleEtaleModuleSheaf_higherDirectImage_of_open_curve`. They use the
same canonical derived direct image, field/subfield encoding, scheme and coefficient
universes. Their finite-field alternative is specialized to the algebraic-closure
alternative here. Every recorded statement dependency is imported, and every recorded
proof-dependency module available in the clone is imported. Unrecorded geometry nodes
are not invented or replaced by private copies. No new definition node or dependency
module is needed in this delivery.

Edge cases: empty T has dimension minus infinity and its open source is empty; empty V
inside nonempty T gives the zero pushforward; d=0 and d=1 retain the sharper bounds
zero and one; any larger d is allowed. The zero coefficient ring and annihilation
exponent n=0 are included. Negative q remain in the constructibility quantifier, and
q=1 for the zero-dimensional case and q=2 for the curve case are covered by the
strict bounds. Vanishing does not assume that M is constructible. There is no
nonempty index-set assumption (no index set is a theorem input), nor a reduced,
connected, separated, or characteristic-zero hypothesis. The universe u is arbitrary;
the scheme, small-etale site and `ModuleCat.{u+1}` coefficient sizes are exactly the
recorded interfaces. Finite coefficient rings can be lifted to this universe, and
there is no extra equality between independent site universes.

Independent searches, using terms different from the author's first query:

- LeanFinder through msearch: “Torsion coefficient etale sheaves pushed across a quasi
  compact open embedding have constructible cohomology sheaves and a dimension dependent
  bound on derived pushforward”. Eight hits: constructible images of scheme subsets,
  structure-sheaf pushforward, sections and site definitions. None is this theorem.
- Loogle through msearch: `"lowerStar"`, zero hits.
- LeanSearch through msearch: “Exact extension by zero and constructible higher direct
  images for an open subscheme of dimension at most one over an algebraic closure of a
  finite field”. Eight hits about restrictions of sections and open covers; none matches.
- Mathlib grep through msearch: `cohomologicalDimension|higherDirectImage.*immersion|IsConstructible.*higher`,
  zero hits.
- Direct rg over Mathlib, upstream `WeilConjectures` and project `lean/Sheaf` used
  `opencomplement|open.complement|constructible.*lowerstar|lowerstar.*constructible|higherdirectimage.*open`
  case-insensitively. The project has the predicate, the two curve dependencies and
  `Scheme.hasOpenComplementCondition_of_isSepClosed` in `OpenComplementUnconditional`.
  I opened the latter: it concludes only the general bound, with a separably closed
  field and positive annihilation exponent. It does not state the clopen exactness,
  extension-by-zero or independent curve clauses, so is not an exact existing binding
  for this full node. The nearby `isBoundedConstructible_rightDerivedLowerStar_of_isOpenImmersion`
  in `OpenDirectImageFiniteCoefficients` concerns bounded complexes and gives neither
  the uniform all-sheaf vanishing bound nor the independent low-dimensional clauses.
  Upstream stability results use different coefficient/categories or conclusions;
  Mathlib structure-sheaf results are not the constant-coefficient etale notion.
- `dag/lean_names_upstream.json` contains neither this theorem's name nor its blueprint
  id. No exact existing statement was found, and no second definition is introduced.

Mismatches and changes: no mathematical mismatch was found. I left the Lean module
and node copy unchanged, as required for correct material, and appended this independent
reading. The author's earlier compiler obstruction is now resolved by the current
standard wrapper: the unmodified command
`python3 /home/ubuntu/weil-launcher-nt/scompile.py N3 lem-exc-open-complement-known lean/Sheaf/AlgebraicGeometry/OpenComplementKnown.lean`
passed overlay compilation, sandbox compilation (3.8 seconds) and library-path
compilation (5.7 seconds), exit zero, without warnings or an overlay environment override.
The old sandbox overlay workaround was not used for this reading or delivery.

Static verification: the node copy differs from the repository node only in `lean`;
`lean.statement` equals the theorem signature verbatim; every Lean line is at most
100 characters; the sole theorem has proof `sorry`; there are no new definitions,
private copies, local instances, local notation, hidden let/show binders, or unbound
variables/universes. The module and theorem docstrings cite the source and blueprint id,
and the theorem docstring follows all fifteen node proof steps. No statement change,
unit change, or unresolved disputed-statement flag is warranted.

Required second-reader dry run: the standard unmodified `deliver2.py N3
lem-exc-open-complement-known --no-push` returned
`OK (dry run): commit 7cb0dc68d9 passes the preflight and compiles; nothing pushed`.
It compiled refreshed dependency overlays and the item without an override. Only the
item module, its node record and this report were staged by the delivery wrapper.
