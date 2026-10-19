## Worker report

The module `Sheaf.TraceFormula.ValuativeDominationEtaNormal` states
`AlgebraicGeometry.valuative_domination_eta_normal` with one `sorry`; it proves
nothing and defines no new notion. The statement is unchanged. It uses the
existing canonical modification and function-field interfaces. Three already
recorded nodes are added to `stmt_deps`: `def-trf-modification`,
`def-sc-function-field`, and `def-pc-reduced-scheme`. No new nodes or dependency
repairs are needed.

The source is Temkin, Stable modification of relative curves, Proposition 5.2,
printed pp. 34–35, with the finite-height reduction in the immediately following
proof of Theorem 1.2 and the eta-normality convention in §3.1. Read directly at
https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf . The node is the
finite-type-over-Z specialization, not a claim for all integral bases.

Hypothesis and conclusion correspondence:

- Integral S: `{S : Scheme.{u}} [IsIntegral S]`. Its generic point is the canonical
  `genericPoint S`, so no chosen generic point or extra point condition is needed.
- Finite type over Z: `s : S ⟶ Spec (CommRingCat.of (ULift.{u} ℤ))`, with
  `[LocallyOfFiniteType s] [QuasiCompact s]`. The lift places the integers in the
  same ring universe as S; it is isomorphic to Z, not a different arithmetic base.
- Function field K: `S.functionField`, Mathlib's local ring at `genericPoint S`,
  with its integral-scheme field instance. The generic map is exactly
  `S.fromSpecStalk (genericPoint S) : Spec S.functionField ⟶ S`.
- C, X, Y over S: `c : C ⟶ S`, `a : X ⟶ C`, `b : Y ⟶ C`; the structure maps of
  X and Y are `a ≫ c` and `b ≫ c`. This includes every diagram in the node since
  a and b are S-morphisms. No extra choice of structure maps is imposed.
- Reducedness: `[IsReduced C] [IsReduced X] [IsReduced Y]`, the recorded
  sectionwise condition equivalent to all local rings being reduced.
- Flatness: `[Flat c] [Flat (a ≫ c)] [Flat (b ≫ c)]`, the recorded flatness class,
  equivalent to flatness of each induced local-ring map.
- Finite type of C, X, Y: each of those three structure maps has both
  `LocallyOfFiniteType` and `QuasiCompact` instances.
- Eta-modifications a and b: `ha` and `hb` use the recorded `EtaModification`
  with the canonical generic map and structure map c. This is properness plus
  an isomorphism on schematically dense source/target opens, and invertibility
  of the actual induced generic base-change map, as specified by the node.
- Eta-normal Y: `hnormal` quantifies over every scheme Z and every map `f : Z ⟶ Y`;
  `IsFinite f` and `EtaModification ... f (b ≫ c)` imply `IsIso f`.
  There is no added flatness, finite-type, or reducedness assumption on Z.
- Valuation subrings V of K with fraction field K: `V : ValuationSubring
  S.functionField`. Its `mem_or_inv_mem'` field is exactly the valuation-ring
  condition; its existing instances make K its fraction field. The inclusion
  used is `V.toSubring.subtype`, not an arbitrary field embedding.
- Finite height: `Finite (PrimeSpectrum V)`. For a valuation ring the primes are
  totally ordered by inclusion, so finiteness of its prime spectrum says exactly
  that its primes form a finite chain; no rank-one or discreteness restriction.
- Every centred map: `∀ v : Spec V ⟶ S`, followed by
  `Spec.map (ofHom V.toSubring.subtype) ≫ v = S.fromSpecStalk (genericPoint S)`.
  This is precisely agreement on Spec K, and it quantifies over every such map.
- The comparison hypothesis: `hvaluative` supplies `hV` in the slice over Spec V
  between the canonical `Over.pullback v` objects for Y and X, and requires
  `hV ≫ a_V = b_V` in that slice. Thus this is a morphism over C_V, not a
  pointwise lift or an unrelated isomorphism of objects.
- Existence of an S-morphism h: the existential is a morphism
  `Over.mk (b ≫ c) ⟶ Over.mk (a ≫ c)`; its defining slice equation is exactly
  `h.left ≫ (a ≫ c) = b ≫ c`.
- Factorization: `h.left ≫ a = b` is the first conjunct.
- Generic fibre: the second conjunct explicitly equates the base change of h
  with `b_eta ≫ inv a_eta`. Lean composes left to right, so this is the node's
  `a_eta^{-1} b_eta`. The inverse uses `ha.2` directly, not an added IsIso premise.

Dependency declarations read and used:

- `def-pc-integral-scheme`: `Mathlib.AlgebraicGeometry.Properties`,
  `AlgebraicGeometry.IsIntegral`, full class fields and integral field instance.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`; and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, `AlgebraicGeometry.QuasiCompact`.
- `def-weil-flat-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Flat`,
  `AlgebraicGeometry.Flat` and its stalkwise equivalence.
- `def-weil-finite-integral-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Finite`,
  `AlgebraicGeometry.IsFinite`; the integral clause `IsIntegralHom` was also read,
  but this statement uses only the finite clause.
- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`; the chosen pullbacks and induced maps are those
  of `CategoryTheory.Over.pullback` (its full definition was read).
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsProper`, used through `SchemeModification.proper`.
- `def-trf-modification`: `Sheaf.TraceFormula.Modification`,
  `AlgebraicGeometry.SchemeModification` and `AlgebraicGeometry.EtaModification`.
  Its schematic-density dependency is `Sheaf.TraceFormula.SchematicallyDenseOpen`,
  `AlgebraicGeometry.SchematicallyDenseOpen`; its section restriction definition
  and the full modification structure/definition were read.
- `def-sc-function-field`: import `Sheaf.AlgebraicGeometry.FunctionField`; its
  documented arbitrary-integral-scheme clause uses Mathlib's
  `AlgebraicGeometry.Scheme.functionField` (the component-product notion is not
  substituted for it). The declaration, docstring, and Mathlib implementation
  were read. No second function field is introduced.
- `def-pc-reduced-scheme`: `Mathlib.AlgebraicGeometry.Properties`,
  `AlgebraicGeometry.IsReduced`, with the local-ring equivalence.
- The valuation subring structure and its `ValuationRing`, `Algebra`, and
  `IsFractionRing` instances were read in
  `Mathlib.RingTheory.Valuation.ValuationSubring`.

The stated proof dependencies are imported without `public`: closed-point field,
flat invertible sections, Abhyankar height, relative dimension zero, proper
fibre-dimension semicontinuity, Nagata morphism descent, flat ring maps,
Noetherian permanence, finite presentation, and proper/quasi-finite finiteness.
The following proof nodes have no Lean declaration in the read DAG, so their
modules cannot yet be imported: `lem-trf-base-modification-comparison-fibre-image`,
`lem-trf-birational-quasi-modification-common-cover`, and
`lem-trf-birational-riemann-zariski-neighbourhoods`. They are proof dependencies
only, not missing objects needed to type this statement; all nine proof steps
remain in the theorem docstring.

Edge cases checked: S is nonempty by integrality; empty C, X or Y are not excluded
by an extra Nonempty hypothesis. No smoothness, normality of S, properness of C/S,
separatedness of X/S or Y/S, or curve-dimension assumption is introduced. The
trivial valuation ring K itself is admitted (one prime); finite chains of any
length, mixed characteristic and positive characteristic are admitted. All
valuation subrings are genuine subtypes of K in universe u, so no independently
small test universe makes the hypothesis vacuous. The modification interface
requires schematic density on both source and target. The generic equality is
between actual canonical morphisms and has the correct composition order.

Searches made:

- `msearch.py ... leanfinder`, query: "A comparison between proper modifications
  of flat reduced schemes exists if it exists over each valuation ring and the
  source is eta normal". Eight results, all ordinary `ValuativeCriterion` point
  lifting/existence/uniqueness declarations; none is this family factorization.
- `msearch.py ... loogle`, query: "EtaModification, SchemeModification,
  ValuationSubring". No hits; service does not index project `EtaModification`.
- `msearch.py ... grep`, query: `eta.normal|valuative.*domination|IsModification`,
  Mathlib `AlgebraicGeometry`. No hits.
- `msearch.py ... leansearch`, query: "A comparison morphism between
  modifications extends from every centred valuation ring if its source is
  eta-normal". Eight results concerning valuation extensions, no match.
- `rg` in upstream `WeilConjectures`, `lean/Sheaf`, `dag/nodes`, and
  `dag/lean_names_upstream.json`, using `EtaModification`, `SchemeModification`,
  `SchematicallyDenseOpen`, `eta_normal`, `valuative_domination`, and the exact
  item id. Existing modification/density notions found and reused. The caller
  StableModificationUniquenessNormal mentions this node in its proof docstring;
  no existing declaration states this theorem. Mathlib valuation rings/subrings
  and function fields were inspected directly rather than redefined.

Compilation: `scompile.py Q122 lem-trf-valuative-domination-eta-normal` compiled
this module cleanly (both sandbox and named-library checks), with no warnings.
The first draft needed explicit target types on `Over.homMk` to resolve its
slice object; these annotations were added without changing the mathematics.
No node fault or statement dispute was found.

## Second reading by Q122

Independent maintainer second reading, 2026-10-18. I did not write or previously
second-read this delivery. I read the immutable item, its nine statement
dependencies, the delivered module and worker report, the actual dependency
implementations, and Temkin's source. This section replaces the delivered
placeholder; it records this maintainer reading, not a claimed group-worker review.

Source checked: Temkin, *Stable modification of relative curves*,
arXiv:0707.3953v3, Proposition 5.2 and proof, printed pp. 34–35;
§3.1, printed p. 14 (modifications and eta-normality); §1.2
(modifications with schematic density); Lemma 2.1.2 and the proof of Theorem 1.2
on printed p. 35 (finite-height reduction).
https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf
The source proposition assumes integral Noetherian S and comparisons at all
points of RZ_K(S). The node deliberately specializes to finite type over Z;
Noetherianness and the finite-height reduction follow. This is the node as
already recorded, not a new statement correction.

Hypotheses and conclusion, independently matched:

- S and its arithmetic base: `{S : Scheme.{u}} [IsIntegral S]` is the
  nonempty integral scheme, and `s` to `Spec (ULift ℤ)` with both finite-type
  instances expresses finite type over Z. ULift changes size only. No
  normality, separatedness, characteristic-zero or smoothness condition on S
  is added. `genericPoint S`, `S.functionField` and `fromSpecStalk` give the
  unique generic point, its stalk field K and the canonical generic morphism.
- The S-schemes and arrows: `c`, `a`, `b` give the entire diagram; X and Y
  have structure maps `a ≫ c`, `b ≫ c`. The three `IsReduced` instances are
  exactly local reducedness by the section/stalk equivalence. The three
  `Flat` instances are stalkwise flatness by `Flat.iff_flat_stalkMap`.
  Each of C, X, Y has both `LocallyOfFiniteType` and `QuasiCompact`, hence
  exactly finite type. Finite presentation is derived in the proof plan,
  not assumed in the signature.
- Modifications: `ha` and `hb` use the dependency's `EtaModification`.
  I opened `Modification.lean` and `SchematicallyDenseOpen.lean`:
  `SchemeModification` requires properness, a target open, schematic density
  of it and its full inverse image, and invertibility of the restriction.
  `EtaModification` additionally requires invertibility of the induced
  slice-pullback map. The section-restriction injectivity definition is
  precisely injectivity of O -> j_*O. These are real predicates, not hollow
  data or arbitrary isomorphisms between fibres.
- Eta-normality: `hnormal` quantifies over every `Z : Scheme.{u}` and map
  `f : Z ⟶ Y`; `IsFinite f` and that same eta-modification predicate imply
  `IsIso f`. There is no extra reducedness, flatness or finiteness-of-type
  premise on Z. The already existing `IsEtaNormal` uses a differently
  packaged generic-fibre interface; no duplicate named notion is introduced
  here, and the node's recorded modification interface is reused.
- Valuations: `ValuationSubring S.functionField` is a genuine subring of K,
  with the valuation membership condition and its `IsFractionRing V K`
  instance. `Finite (PrimeSpectrum V)` means a finite chain of primes,
  since valuation-ring primes are linearly ordered. This does not restrict
  to rank one or to discrete valuations. The inclusion is the actual
  `V.toSubring.subtype`. Every centre map v is universally quantified,
  followed by precisely the required equality on Spec K.
- Comparisons: `Over.pullback v` uses the chosen scheme fibre products.
  I read its implementation: objects use `pullback.snd`, and morphisms use
  the canonical `pullback.lift`. Thus the existential `hV` is a morphism
  over Spec V, and its displayed equation is exactly `hV ≫ a_V = b_V`.
  This supplies a comparison of whole families over C_V.
- Conclusion: the existential h is in the slice over S, so it is an
  S-morphism. `h.left ≫ a = b` gives the required factorization.
  The final equality is equality of actual canonical generic maps,
  `h_eta = b_eta ≫ inv a_eta`. The inverse takes `ha.2`, not an additional
  hypothesis. This is exactly the node's composition a_eta^{-1} b_eta.

Dependency records and implementation checks:

I read all nine statement dependency records in the snapshot, not just the
packet's names. The underlying declarations were checked in the read-only
Mathlib checkout: Properties.lean (`IsIntegral`, `IsReduced` and their
instances/equivalences), Morphisms/FiniteType.lean and QuasiCompact.lean,
Morphisms/Flat.lean, Morphisms/Finite.lean, Morphisms/Proper.lean,
Limits/Shapes/Pullback/HasPullback.lean, and Comma/Over/Pullback.lean.
`IsFinite` is affine plus finite section algebra; `IsProper` includes
separatedness, universal closedness and local finite type, with
quasi-compactness supplied by universal closedness. The unused integral
clause of the finite/integral dependency is not substituted for finiteness.
For `def-sc-function-field`, I opened its recorded FunctionField module and
Mathlib/AlgebraicGeometry/FunctionField.lean: the node explicitly permits
Mathlib's generic stalk for arbitrary integral schemes. The product over
components is not mistakenly used as K.

I searched the read-only upstream WeilConjectures tree, group lean/Sheaf,
and Mathlib's AlgebraicGeometry tree for `valuative.domination`, `eta.normal`,
`EtaModification` and `SchemeModification`. The existing modification and
eta-normality interfaces and the uniqueness consumer were inspected; no
existing theorem with this valuative family-domination statement was found.
The worker additionally records LeanFinder/Loogle/LeanSearch searches and
their results. No new definitions or private copies are delivered, so there
is no missing-helper construction or universe transport to repair.

Proof plan checked against the item and its cited proof-node statements:

1. Noetherian permanence, finite-presentation over a Noetherian ring, and
   the Abhyankar height bound supply the stated reductions.
2. The flat affine criterion and torsion-free-section lemma give generic
   density after integral base change. Properness gives the closed equalizer
   needed for uniqueness; the structure sheaf is an allowed invertible module.
3. The fixed-field Riemann–Zariski neighbourhood statement supplies the
   filtered rings, open neighbourhoods and quasi-compactness. Morphism
   descent is applied to the C-base-changed system with finite presentation.
4. The common-cover statement supplies the base modification and opens.
   Generic uniqueness glues the maps; the node explicitly justifies the
   dense base open where the modification is an isomorphism.
5–6. The generic graph closure, its open graph locus, schematic density,
   reducedness, proper projection and proper surjection are all described.
   Properness/permanence and generic density are used with their hypotheses.
7. The fibre-image assertion is a separately cited proof prerequisite,
   with eta-normality available here. The subsequent finite residue-field
   tensor calculation uses a closed point of the finite-type fibre Y_s.
   The invalid direct inference from a quasi-finite image over S'_s to one
   over s is not used as a proof in this module; the source gap is already
   isolated in the DAG prerequisite.
8. Proper fibre-dimension semicontinuity extends the bound from closed
   points in the Noetherian scheme Y; proper locally quasi-finite implies
   finite. The projection is then a finite eta-modification, exactly the
   case covered by hnormal.
9. The inverse projection and fibre-product identity give the two required
   conclusion clauses. This last composition step is elementary.

These are the nine steps in the declaration docstring. Proof dependencies
without Lean records are proof prerequisites only: no object required to
state this theorem is missing. They need not be constructed to type this
stage-2 statement. There is no new helper theorem whose proof or DAG record
is hidden in this delivery.

Edge cases and universes:

S cannot be empty by integrality. Empty C, X or Y are not independently
excluded; any forced emptiness is governed by the modification assumptions.
The trivial valuation V=K is included, as are finite chains of arbitrary
length. Positive and mixed characteristic are included. No curve dimension,
properness over S, or separatedness over S is imposed on C, X or Y.
All binders and the universe u are explicit, with both automatic-implicit
options disabled. Subrings and prime spectra have the universe of K;
there is no smaller independent valuation universe or forced site/coefficient
universe equality. Generic base change and the test schemes use the same
ordinary scheme universe convention as the dependency interfaces.

Mechanical and compiler checks:

- The node's `lean.statement` is byte-for-byte the signature in the
  delivered module, from `theorem` through the type before `:= by`.
- The module and declaration docstrings contain the source and blueprint
  id. All nine proof steps are present. All lines are at most 100 characters.
- The module contains one theorem with proof `by sorry`, no new definitions,
  local proofs, axioms, constructions from arbitrary maps or hollow data.
- All statement/proof dependency ids were compared with
  `origin/newtargets-dag:coord/route-pivot-dropped.txt`: empty intersection.
  No route-pivot repair note exists for this item at that ref. The delivery
  contains no infinity/dg/model-category or pro-etale substitute.
- Reproduced the immutable file with
  `python3 /home/ubuntu/weil-launcher-nt/scompile.py Q122
  lem-trf-valuative-domination-eta-normal <absolute snapshot module path>`.
  Exit code 0. Sandbox `Sheaf/Stage2/Sandbox0.lean`: 4.8 s;
  named-library `Sheaf/TraceFormula/ValuativeDominationEtaNormal.lean`: 23.0 s.
  Neither emitted diagnostics. The installed wrapper identifies itself as
  the 2026-10-17 server-side persistent-overlay wrapper; its output records
  a private `/dev/shm/nt-tmp/nt-local-compile-w1hbjsif/.lbuild` overlay.
  I used this prescribed wrapper only, with no direct ssh invocation,
  lake build, global build, live Lean write or project-clone edit.

Finding and repair: H11 (also the substantive second-reading requirement in
H1): the delivered section merely disclaimed a second reading. I replaced
that placeholder with this actual independent reading. I also corrected the
worker report's source pointer for the eta-normality convention from §3.3
to §3.1. The Lean module and JSON record need no change. No substantive
statement fault or unintended stronger assumption was found.
