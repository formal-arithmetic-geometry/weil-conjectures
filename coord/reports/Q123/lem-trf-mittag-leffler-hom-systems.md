## Worker report

The module Sheaf.RingTheory.MittagLefflerHomSystems states
Module.hom_images_stabilize_of_isMittagLeffler. Its sole theorem has proof
sorry. No definition, helper theorem, new node, dependency repair, or statement
correction is introduced. The node changes only in lean.

Read the complete item statement and six-step proof, both statement dependencies
and their declaration signatures and docstrings, and Stacks algebra.tex,
proposition-ML-tensor (Tag 059M), implication (2) to (1), and
proposition-ML-characterization (Tag 059E), especially (2) to (3) to (4).
The theorem docstring carries all six steps of the node's proof.

Clause-by-clause comparison:

- Commutative ring: (R : Type u) [CommRing R].
- Small nonempty directed partially ordered set: {I : Type v}
  [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]. Mathlib equips it
  with the small category of inequalities.
- Directed system: F : I ⥤ ModuleCat.{max u v w} R. Functor laws are the
  system identities. The transition is (F.map (homOfLE hij)).hom.
- Every stage is finitely presented:
  [∀ i : I, Module.FinitePresentation R (F.obj i)]. This is Mathlib's
  finite generators and finitely generated relations, equivalent to the
  node's cokernel of a finite matrix. Its exists_fin theorem presents the
  module as (Fin n → R) modulo a finitely generated submodule, so zero
  generators and zero relations are included.
- Compatible maps M_i → M exhibiting a colimit: c : Cocone F and
  hc : IsColimit c. The module M is c.pt, its structure maps are c.ι.app i,
  compatibility is naturality, and IsColimit contains universal factorization
  and uniqueness. Any specified colimit cocone is allowed.
- Tensor-product Mittag-Leffler condition: hM applies exactly the dependency
  Module.IsMittagLeffler to R and c.pt. Its index and test-module universe is
  max u v w, sufficient for all finite-matrix modules and their tensor-kernel
  elements in the source proof. The final 0 in the explicit universe list
  gives test modules in max u (max u v w) 0, that same ambient universe.
  The ring, index and module sizes have independent parameters within a
  common ambient universe; increasing it permits any small system. No
  inverse-system hypothesis is substituted for the tensor-product condition.
- Arbitrary target: (N : Type t) [AddCommGroup N] [Module R N], with an
  independent universe and no finiteness assumption.
- Every i has a later j: ∀ i : I, ∃ (j : I) (hij : i ≤ j).
- Every k later than j: ∀ (k : I) (hjk : j ≤ k).
- Equality of the two precomposition images: the equality of Set.range of
  a ↦ a.comp (F.map (homOfLE (hij.trans hjk))).hom and
  a ↦ a.comp (F.map (homOfLE hij)).hom, with domains respectively
  F.obj k →ₗ[R] N and F.obj j →ₗ[R] N. Both ranges are subsets of
  F.obj i →ₗ[R] N. Equality as subsets is equality of the image submodules.
  The quantifier for j follows N and i exactly as in the node.
- No countability hypothesis on I and no finite-generation condition on N
  appears, nor flatness or injectivity assumptions on the transition maps.

Dependency declarations used:

- def-trf-mittag-leffler-module: Module.IsMittagLeffler from
  Sheaf.RingTheory.IsMittagLeffler. Read the shared file and the current
  server source with scompile.py --source; they agree. Its comparison map
  is Mathlib's TensorProduct.piRightHom, with the required pure-tensor formula.
- def-weil-pbc-category-colimit: CategoryTheory.Limits.Cocone and
  CategoryTheory.Limits.IsColimit, explicitly listed by its lean record,
  imported through Mathlib.CategoryTheory.Limits.HasLimits. Read the complete
  structure signatures, including desc, fac and uniq.
- The recorded proof dependency def-sc-finitely-presented-module supplies
  Module.FinitePresentation from Mathlib.Algebra.Module.FinitePresentation;
  it also occurs in the signature.
- The Mathlib proof dependencies on tensor-colimits and elementwise filtered
  colimits are imported through TensorProduct.DirectLimit,
  ModuleCat.FilteredColimits and Limits.ConcreteCategory.WithAlgebraicStructures.
  Tensor product data and maps are already imported by the ML definition.
- The proof-only nodes lem-trf-finite-presentation-tensor-products and
  lem-trf-tensor-kernel-factorization have no lean record in the read-only DAG
  at this writing. They are named in the proof docstring. No notion from their
  statements is needed to type the signature. The maintainer can add their
  imports once they are stated, as the stage rules prescribe.

Edge cases checked against the node and source: zero ring, zero stage modules,
zero colimit and zero target are allowed; singleton and arbitrarily large
nonempty directed posets are allowed. Empty posets are excluded exactly by the
node. Reflexivity allows j = i and k = j. Noninjective and zero transitions
are allowed. The target can be infinitely generated and in another universe.
The ML dependency includes the empty product family. No case requires flatness.

Searches actually made in this attempt:

- msearch.py leanfinder: Tensor-product Mittag Leffler module implies
  stabilization of images of precomposition Hom maps for a directed colimit
  of finitely presented modules. Eight hits on tensor/direct limits and
  finitely generated submodule tensor diagrams, none stating this bridge.
- msearch.py leansearch: Tensor product Mittag Leffler modules have Mittag
  Leffler inverse systems Hom from finitely presented stages. Eight hits on
  tensor finite presentation and tensor/direct limits, none giving the bridge.
- msearch.py loogle: quoted Mittag. Nine hits, principally
  CategoryTheory.Functor.IsMittagLeffler and its inverse-system lemmas. They
  do not infer stabilization from tensor-product injectivity.
- msearch.py grep: Mittag|mittag|059M|059E. Nine hits on CofilteredSystem,
  an adic-completion comment and unrelated cotangent partial fractions.
- rg of WeilConjectures and lean/Sheaf for mittag|Mittag finds the landed
  module definition and unrelated cofiltered-system, cohomology and completion
  results, not this theorem. grep -rn for the node id in WeilConjectures gives
  no hit. rg for Mittag in dag/lean_names_upstream.json finds the short exact
  sequence and countable-section lemmas, not the item.
- Searched the proposed declaration name in Mathlib, upstream and side
  sources; no earlier declaration found.

No mathematical defect or disputed statement was found. The reviewed stage-1
split is retained verbatim. Validation results are recorded below.

Validation: scompile.py compiled this file cleanly both as the sandbox probe
and under its final library module name. There were no errors or warnings.

## Second reading by Q123

Independent maintainer second reading, 2026-10-18, of immutable delivery
e2eaefd7d7a5d4bf7155d24ee1c7ac724fd55016. I did not write or previously
second-read this delivery. Read packet.md, the complete check-brief2.md, the
snapshot item, both statement dependencies, delivered module and report, and
the actual declarations and source passages described below.

Clause-by-clause reading (all pass):

- Ring: `(R : Type u) [CommRing R]` is an arbitrary commutative ring.
- Index: `{I : Type v} [PartialOrder I] [Nonempty I]
  [IsDirected I (· ≤ ·)]` is precisely the node's small nonempty directed
  partially ordered set. There is no countability assumption.
- System: `F : I ⥤ ModuleCat.{max u v w} R` supplies every stage and transition;
  its functor laws supply the directed-system identities. `homOfLE` supplies
  the order arrows and `.hom` the corresponding linear maps.
- Finite presentation: `[∀ i : I, Module.FinitePresentation R (F.obj i)]`
  uses the existing ordinary-module notion. Read its class definition and
  `Module.FinitePresentation.exists_fin` and `exists_fin'` in Mathlib,
  Algebra/Module/FinitePresentation.lean:67,84,95. The finite generating set
  and finitely generated kernel give exactly a cokernel of a finite matrix,
  including zero generators or relations. No sheaf presentation, coherence,
  Noetherian condition, or flatness is substituted.
- Colimit: `c : Cocone F` and `hc : IsColimit c` supply the specified module
  `c.pt`, compatible maps `c.ι.app i`, and their universal property. Read
  `Cocone` in CategoryTheory/Limits/Cones.lean:133 and `IsColimit` in
  CategoryTheory/Limits/IsLimit.lean:62, including `desc`, `fac`, and `uniq`.
  These are explicitly listed in def-weil-pbc-category-colimit's record.
  The statement allows any given colimit cocone, without requiring a chosen
  colimit object or extra transition-map assumptions.
- Mittag-Leffler: `hM` uses the actual recorded
  `Module.IsMittagLeffler` from Sheaf.RingTheory.IsMittagLeffler, not the
  unrelated predicate on inverse systems. Read its complete definition and
  docstring at /home/ubuntu/weil-newtargets-Q123/lean/Sheaf/RingTheory/
  IsMittagLeffler.lean:23-36. It quantifies over families of genuine modules
  and uses `TensorProduct.piRightHom R R P Q`. Read that construction and
  `piRightHom_tmul` in Mathlib/LinearAlgebra/TensorProduct/Pi.lean:47-62:
  its pure-tensor formula is exactly the node's canonical comparison.
- Universes: put U = max u v w. The specialization
  `IsMittagLeffler.{u, U, U, 0}` tests index types in Type U and modules in
  Type (max u U 0) = Type U. It does not reduce the tests to finite families
  or to a universe smaller than R or the stages. The finite-matrix
  representatives can be lifted into U; their tensor kernels with M_i and
  the set of pairs (matrix, kernel element) are U-small. Thus the universal
  product used by the proof fits this exact ML hypothesis. The common
  ambient universe contains both the ring and the indexing type, as needed
  for filtered colimits of modules; u and v are not equated. All small
  systems admit this ambient size (using the standard universe lifts when
  necessary), and the independent universe t of the target is unrestricted.
  Every universe and term variable in the signature is explicitly bound.
- Target: `(N : Type t) [AddCommGroup N] [Module R N]` is arbitrary, even
  infinitely generated or larger than the stages. It is quantified before i
  and the existential j, exactly as in the node.
- Stabilization: `∀ i, ∃ (j : I) (hij : i ≤ j), ∀ (k : I) (hjk : j ≤ k)`
  gives precisely the required tail. The first `Set.range` consists of
  `a.comp (F.map (homOfLE (hij.trans hjk))).hom` for a from M_k to N; the
  second consists of `a.comp (F.map (homOfLE hij)).hom` for a from M_j to N.
  Both are subsets of M_i →ₗ[R] N. Their equality is exactly equality of
  the two precomposition images, with the correct direction and no clause
  missing. Equality of the underlying sets also gives equality as image
  submodules.

Source and proof audit:

Read /home/ubuntu/weil-newtargets-Q123/literature/stacks-project/algebra.tex,
20910-21110 (domination and proposition-ML-characterization, Tag 059E) and
21330-21540 (proposition-fp-tensor, Tag 059K; lemma-kernel-tensored-fp,
Tag 059L; proposition-ML-tensor, Tag 059M). No hidden finiteness, flatness,
countability, or nonzero-ring assumption occurs in these results.

All six node proof steps are mathematically supported and appear in the
Lean theorem's docstring: finite-matrix representatives give a set of all
kernel tests; finite presentation lifts their family to one tensor element;
ML injectivity kills its colimit image; tensor-colimit compatibility and
an elementwise filtered-colimit test kill it at one later stage j; finite
presentation of the transition cokernel permits tensor-kernel factorization;
composing with that factorization and with the system transition gives the
two opposite Hom-image inclusions. The kernel inclusion in steps 3-5 has the
correct direction. A single j works for all finitely presented tests, hence
for all k ≥ j. The proof need only use the weaker k ≥ j tail, even though
059E(3) supplies a factorization for all k ≥ i.

Read the statements and records of the six proof-only prerequisites in the
group clone as well. The two tensor/Hom bridge lemmas have no recorded Lean
modules; neither is an absent object needed to type this statement. Their
proof-only use in the docstring is appropriate for stage 2. The existing
Mathlib tensor-colimit and elementwise-colimit imports are proof-plan
imports allowed by brief-stage2.md §3. No missing-helper repair or unstated
statement prerequisite is required. No statement_change was made or is
needed, so a correction/citer audit under §1(C) is inapplicable.

Edge cases: the zero ring, zero stages, zero colimit, zero target, zero maps,
noninjective transitions, zero generators and zero relations are allowed.
Empty I is excluded exactly as the node requires; singleton and uncountable
directed I are allowed. Reflexivity permits j = i and k = j. The ML
predicate includes the empty test family. No characteristic restriction or
finite generation of N is introduced.

One-definition-per-notion and pilot checks:

An independent msearch.py leanfinder query, "Tensor injectivity for products
forces eventual equality of restriction images of linear maps out of finitely
presented stages of a filtered colimit", returned eight tensor/direct-limit
and finite-generation results, not this bridge. Independent rg searches of
Mathlib, upstream WeilConjectures, and group lean/Sheaf for Mittag, 059M,
059E, and the proposed declaration name found no duplicate theorem.
Mathlib's CategoryTheory.Functor.IsMittagLeffler (CofilteredSystem.lean:132)
was opened: it defines stabilization for a functor into sets, without deriving
it from tensor-product injectivity. The module predicate is reused, not
redefined. The worker report records all three required search kinds.

The sole delivered theorem has exactly `by sorry`; there are no definitions,
local proofs, axioms, private copies, arbitrary maps, or hollow constructions.
Both module and declaration docstrings cite the source and blueprint id.
The declaration docstring follows all six node proof steps. Every line of the
Lean file is at most 100 characters. Automated literal comparison confirms
that lean.statement is verbatim the signature from `theorem` through the
conclusion, excluding `:= by`. Read-only git show/diff confirms that the
commit adds only this module, the report, and the item's lean record; no
other item field changes. The full name and topic directory are appropriate.

Read the current origin/newtargets-dag:coord/route-pivot-dropped.txt through
read-only git show; neither statement nor proof dependencies intersect it.
There is no item-specific repair note at the specified route-pivot path.
This is ordinary module algebra and introduces none of the dropped
infinity/dg/model-category machinery or any pro-etale substitute.

Finding and correction: H11 (also the explicit real-second-reading gate).
The delivered `## Second reading by Q123` was only a disclaimer and was not
a reading. This section supplies the independent reading, with the worker
report retained above. No mathematical or Lean-file correction is needed.

Compiler reproduction and final checks:

Ran the prescribed wrapper from the review directory:

```
python3 /home/ubuntu/weil-launcher-nt/scompile.py Q123 lem-trf-mittag-leffler-hom-systems snapshot/lean/Sheaf/RingTheory/MittagLefflerHomSystems.lean
```

The completed invocation returned exit code 0, with no errors or warnings:

```
sandbox Sheaf/Stage2/Sandbox0.lean

(with the modules compiled into /dev/shm/nt-tmp/nt-local-compile-ahjb5u4v/.lbuild) [79.1 s]
library Sheaf/RingTheory/MittagLefflerHomSystems.lean

[165.5 s]
```

The installed scompile.py now delegates to the server's persistent side-overlay
compiler (`nt_srv_compile.py --wire-confirm`), rather than the earlier local
implementation described in the brief. This was invoked only through the
prescribed wrapper. Its progress explicitly retained the 60-second limit after
slot acquisition, and nt_srv_compile.py/nt_lcompile.py confirm the two-thread,
nice-19 per-file policy; elapsed wrapper timings include waiting/offload.
Initial SSH-multiplexing notices were transport progress, not Lean diagnostics.
No global build, direct SSH command, live Lean write, delivery, claim, or merge
was performed. The recorded worker compile is reproduced successfully.

Read-only git object comparisons also confirmed that all three delivered
snapshot files exactly match the requested immutable commit. In particular,
the unchanged Lean module's SHA-256 is
`a91a4d45600cab66ba33a336990d45a835ccfa5361c145f6bb201ff813b529f1`.

Final finding: H11 is repaired completely by the replacement report. The
worker section is retained verbatim, and the real second-reading section now
records every hypothesis/conclusion, sources, universes, edge cases, searches,
compiler evidence, and the correction. No H3/H4/H5/H6/H7/H8/H9/H10/H12/H13
substantive defect was found. Verdict FIX; apply only the complete replacement
report in fixes/lem-trf-mittag-leffler-hom-systems.report.md.
