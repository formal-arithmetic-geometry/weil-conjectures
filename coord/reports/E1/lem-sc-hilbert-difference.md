## Worker report

The module defines `tensorIntPow`, the integer tensor power of an invertible module (ordinary tensor powers for nonnegative integers and dual tensor powers for negative integers), and states `AlgebraicGeometry.Scheme.Modules.hilbert_difference`. The theorem uses the recorded proper morphism, locally Noetherian, coherent-module, invertible-module, and topological Krull-dimension declarations. It models the regular meromorphic section by `s : unit X ⟶ meromorphicModule X L` with `Mono (meromorphicSectionMap X L s)`, and takes the denominator module as the pullback of `s` along `toMeromorphicModule`; `Q` and `Q'` are the cokernels of its two projections. The hypotheses are: a field and scheme over its spectrum, properness, nonemptiness, local Noetherianity, finite dimension `hDim`, coherence of `F`, full support via non-subsingleton stalks, and the affine-local condition that all associated primes of `F` are minimal. The conclusion states injectivity of both maps, coherence of both cokernels, strict topological-dimension drop of both stalk supports, and the Euler-characteristic forward-difference identity for every integer `n`, using `tensorIntPow`.

The theorem imports and uses `Sheaf.AlgebraicGeometry.MeromorphicDenominatorIdeal`, specifically the existing declaration `AlgebraicGeometry.Scheme.Modules.meromorphic_denominator_ideal_nowhere_dense`, as the recorded denominator-ideal infrastructure; `Sheaf.AlgebraicGeometry.Coherent` for `RingedSpace.IsCoherent`; `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar` for `Scheme.Modules.eulerChar`; and `WeilConjectures.AlgebraicGeometry.Modules.Dual` for negative tensor powers. The properness, local-Noetherianity, invertibility, and Krull-dimension dependencies are recorded Mathlib/project declarations in the node.

Edge cases checked in the statement are `n = 0`, negative integers (handled by dual powers), the empty support of either cokernel (the subtype Krull dimension is bottom), and the nonempty hypothesis on `X` required by the dimension-drop conclusion. The module compiled cleanly with `scompile.py` when both delivery modules were supplied together.

Searches: `msearch.py leanfinder "coherent sheaf regular meromorphic section denominator ideal cokernel nowhere dense"` found no matching theorem; `msearch.py loogle "forward difference polynomial degree"` found no hit; grep for `forward difference|meromorphic section|denominator ideal` in Mathlib AlgebraicGeometry found no hits. Searches for integer tensor powers (`leanfinder`, `loogle`, and grep for `tensorIntPow|integer tensor power`) found no declaration, so the new definition node `def-sc-invertible-tensor-integer-power` was added.

## New nodes

- `def-sc-invertible-tensor-integer-power`: supplies the missing integer tensor-power notion used by the source statement.

## Earlier second reading (a previous round; superseded)

I read the item and each statement dependency. The Lean binders match the field, scheme-over-field, proper, nonempty, locally Noetherian, finite-dimension, coherent, full-support, no-embedded-associated-primes, invertibility, regular-meromorphic-section, and integer-twist hypotheses. The `let` binders identify the denominator module as the pullback and the two cokernels as the cokernels of its projections. The conjunctions state injectivity, coherence, and strict dimension drop for both cokernels, and the final universal integer clause is the displayed Euler-characteristic forward difference with the same signs. The added integer tensor-power definition is required because the existing project `tensorPow` is indexed only by `ℕ`; it uses the dual for negative exponents and keeps the source's all-integer quantifier.


## Second reading by E1

Independent second reader: read the original and sandbox item, its source, every statement
 dependency record and declaration, the new definition node, and both delivery modules.
The earlier second-reading paragraph is superseded by this reading. The original Lean
DID NOT say what the node said: its Q and Q' were cokernels of I -> O_X and I -> L,
so they ignored F. This was repaired without changing the item's mathematical statement.

Source reading: this checkout has no literature/stacks-project/*.tex. Retrieved the original
Stacks divisors.tex and varieties.tex into this sandbox's scratchpad and read
lemma-make-maps-regular-section (Tag 02P2, currently Lemma 31.25.5), its surrounding
Noetherian discussion, and lemma-numerical-polynomial-from-euler (Tag 0BEM), including
its section introduction and full proof. Also checked the rendered tag pages:
https://stacks.math.columbia.edu/tag/02P2 and https://stacks.math.columbia.edu/tag/0BEM.
02P2 assumes local Noetherianity, invertibility, regularity, coherence, full support and
no embedded associated points. It constructs IF -> F and IF -> F tensor L.
0BEM supplies properness over a field and the Euler subtraction; reversing BOTH
subtractions gives precisely the forward-difference signs in this node. The node takes
s as an input, so the extra no-embedded-components condition used to FIND s is unnecessary.

Object/hypothesis/conclusion checklist, with final Lean and verdict:

- k a field: `{k : Type u} [Field k]`. Exact; arbitrary characteristic, no algebraic closure.
- X a scheme over k: `{X : Scheme.{u}} [X.Over (Spec (.of k))]`. Exact recorded convention.
- Proper over k: `[IsProper (X ↘ Spec (.of k))]`. Read Mathlib IsProper: separated,
  universally closed and locally finite type; universal closedness supplies quasi-compactness
  and hence finite type, matching def-weil-proper-morphism. Exact.
- X nonempty: `[Nonempty X]`. Exact explicit hypothesis of the node.
- Locally Noetherian: `[IsLocallyNoetherian X]`. Read Mathlib's affine-open Noetherian-ring
  class and pqf-def-locnoeth's equivalence with an affine Noetherian cover. Exact.
- Finite dimension: `(d : ℕ) (hDim : topologicalKrullDim X = (d : WithBot ℕ∞))`.
  Exact for nonempty X; topologicalKrullDim is Order.krullDim of IrreducibleCloseds.
- F an O_X-module: `(F : X.Modules)`. Same module-sheaf category as the dependencies.
- F coherent: `hFcoh : RingedSpace.IsCoherent X.toRingedSpace F`. Opened Coherent.lean:
  finite type plus finite-type kernels of maps from all finite free restrictions. Exact.
- Supp(F) = X: `hFsupport : ∀ x, ¬ Subsingleton ((presheaf F).stalk x)`.
  Every stalk is nonzero, exactly full support. Exact.
- No embedded associated points: `hFnoEmbedded` says every associated prime on every
  affine open is Minimal among associated primes of Γ(F,U). Read associatedPrimes and
  IsAssociatedPrime in Mathlib/RingTheory/Ideal/AssociatedPrime/Basic.lean. On Noetherian
  affine opens the minimal associated primes are precisely the minimal primes of the
  support; with full support this is the node's no-embedded-points condition. Exact.
- L invertible: `(L : X.Modules) [L.IsInvertible]`. Read the recorded upstream
  IsInvertible.exists_isoUnit definition: locally structure-sheaf rank one. Exact.
- K_X and K_X(L): `meromorphicModule X (unit X)` and `meromorphicModule X L`.
  Opened MeromorphicModule.lean: sheafification of sections localized at stalkwise
  non-zero-divisors; its tensor comparison for invertible L identifies the latter with
  K_X tensor L. This is the existing notion, no private replacement. Exact.
- s global meromorphic section: `s : unit X ⟶ meromorphicModule X L`.
  Global sections are equivalently O_X-linear maps from O_X. Exact.
- Regularity: `hs : Mono (meromorphicSectionMap X L s)`. Read the defining unique
  localization extension theorem and definition; this is injectivity of K_X -> K_X(L),
  not merely of O_X -> K_X(L). Exact.
- Denominator I: pullback of s and `toMeromorphicModule X L`, with projections i and j.
  Read MeromorphicDenominatorIdeal.lean: the first clause identifies sections with
  a such that a*s lies in L. The recorded theorem uses exactly this pullback. Exact.
- IF: **repaired** to `idealModuleProduct i F`, imported from
  Sheaf.AlgebraicGeometry.IdealModuleProductStalk. Its definition is the image of
  `μ := i ▷ F ≫ (λ_ F).hom`, sending a tensor m to am. It is already recorded under
  lem-weil-pbc-ideal-module-product-stalk; no new definition of IF was written. Exact.
- IF -> F: **repaired** to `iF := idealModuleProductι i F`, the existing image inclusion.
- IF -> F tensor L: **repaired** to `∃ jF : idealModuleProduct i F ⟶ tensorObj F L`
  with `factorThruImage μ ≫ jF = j ▷ F ≫ (β_ L F).hom`.
  This equation says a*m is sent to m tensor (a*s), including tensor symmetry.
  The image factor is epi, so jF is unique and is the source's canonical map.
  Existence and factorization are conclusions, not extra hypotheses. Exact.
- Both injective: **repaired** to `Mono iF ∧ Mono jF`. Exact.
- Q and Q' the respective cokernels: **repaired** to `cokernel iF` and `cokernel jF`.
  Every later coherence, support and Euler clause now refers to these F-dependent objects.
- Both coherent: `IsCoherent ... Q ∧ IsCoherent ... Q'`. Exact.
- Both supports of smaller dimension: both `topologicalKrullDim` of the subtype
  `{x | ¬ Subsingleton ((presheaf Q).stalk x)}` (and Q') are strictly below dim X.
  The subtype has the induced topology, as def-kun-topological-krull-dimension requires.
  Exact, separately for both supports.
- All integer twists: `∀ n : ℤ` and `tensorIntPow L n`. Exact quantifier and exponent n+1.
- Euler identity: χ(F tensor L^(n+1)) - χ(F tensor L^n) =
  χ(Q' tensor L^n) - χ(Q tensor L^n). Read upstream eulerChar/finrankH definitions:
  alternating finsum of k-vector-space cohomology dimensions; proper coherent finite
  dimensional context makes this the finite Euler characteristic. Exact signs and objects.

Edge cases: empty X is explicitly excluded by the node and Lean. The zero F is excluded
by full support and nonempty X, exactly as in the node; zero Q or Q' IS allowed, with
empty support having dimension bottom. Dimension d=0 is allowed and forces both supports
empty, so the identity is zero. n=0 gives the unit tensor power; n=-1 crosses the dual/unit
boundary correctly; all other negative integers use powers of the dual. There is no
index set in this lemma, hence no empty-index restriction. No restriction on characteristic.
The arbitrary universe u matches the existing Scheme.Modules and schemes over fields
encoding; no independent lower test universe or hidden extra instance is introduced.
All variables and universes are bound; combined server compilation produced no warnings.

New-node review (H12): def-sc-invertible-tensor-integer-power really supplies the absent
integer-indexed sheaf power, not Mathlib's natural-indexed TensorPower of ring modules.
Read upstream tensorPow (0 = unit; successor = L tensor previous power) and dual
(Hom(L,O_X)), and the invertible-module node that already specifies duality. Negative
powers in IntegerTensorPower.lean are therefore exactly the inverse tensor powers of 0BEM.
The definition has real data and no sorry. Repaired the new node's circular nonnegative
wording to specify zero and iterated copies, and added def-pur-sheaf-tensor-product to its
statement and stmt_deps. Opened that dependency's recorded tensor definition. Checked
new-node id, chapter/unit, blueprint ancestor/via, source, status split, created fields,
empty proof/proof_deps, null match, lean_audit none and lean record. No dependency module
was added. The item's own statement and proof are unchanged, so no statement_change or
citer verdict is applicable.

Independent H4 searches (run through msearch.py, recorded in searches.jsonl):
- LeanFinder `image ideal sheaf multiplication coherent module Euler characteristic
  difference`: returned ideal-sheaf data/kernel/localization statements, no target theorem.
- LeanFinder `tensor power of an invertible sheaf indexed by integers using its dual`:
  returned CommRing.Pic.mk_tensor/mul_eq_tensor and presheaf monoidal declarations;
  these are ring Picard classes or binary tensor operations, not integer sheaf powers.
- Loogle `"tensorPow"`: natural-indexed TensorPower and related graded algebra results,
  no integer powers of invertible sheaves.
- LeanSearch `integer powers of line bundles defined by dual tensor powers` and
  `Euler characteristic difference tensor invertible sheaf cokernels`: both services
  returned Internal Server Error. Recorded as unavailable, not as negative evidence.
- msearch grep `tensorIntPow|integer tensor power|negative tensor power|hilbert_difference`
  over all Mathlib: zero hits. Direct rg with integer/power/zpow/tensor alternatives
  over upstream WeilConjectures, project lean/Sheaf and dag/nodes found only the natural
  tensorPow, related proof prose, and the existing idealModuleProduct notion cited above.
  No DAG definition of integer powers or existing hilbert_difference was found.
Updated the new node's search records to these actual searches instead of unsupported
claims of successful negative LeanSearch results.

Other repairs: expanded the statement docstring to the node's four proof steps with all
supporting node names; corrected the docstring's 02P2 lemma number to 31.25.5; supplied
standard copyright headers; removed the redundant direct Dual import and used the existing
IdealModuleProductStalk import for its definitions and tensor machinery. The only theorem
still has `by sorry`, as required in stage 2. Both modules compiled together cleanly via
scompile.py (exit 0, 4.6 seconds). The item's lean.statement was synchronized verbatim
with the final theorem signature. No hollow definition or private mathematical copy remains.

## Reviewer fix (R-hdf1258)

- H12/H4: the new node def-sc-invertible-tensor-integer-power and its `tensorIntPow` were a second form of the integer twist, which H1's landed lem-sc-snapper-numerical-polynomial writes inline as `if 0 ≤ n then L.tensorPow n.toNat else L.dual.tensorPow (-n).toNat`. The node and module are dropped; the item's added stmt_dep is reverted; the theorem uses the inline form.
- `let` binders removed from the statement: I, i, j, μ, iF, Q, Q' are written out as `pullback.fst/snd s (toMeromorphicModule X L)`, `idealModuleProductι`, `cokernel`.
