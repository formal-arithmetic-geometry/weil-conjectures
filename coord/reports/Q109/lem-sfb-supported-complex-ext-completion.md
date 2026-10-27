## Worker report

The delivery states `DerivedCategory.supportedComplex_ext_completion` in
`Sheaf.RingTheory.SupportedComplexExtCompletion`. Its sole postponed theorem
has proof `sorry`; all helper definitions contain actual constructions.
The original node statement, statement dependencies and proof remain unchanged.
No disputed statement, new node, or dependency repair is needed.

Clause-by-clause translation:

- The commutative Noetherian ring is `{A : Type u} [CommRing A]
  [IsNoetherianRing A]`; its ideal is `I : Ideal A`.
- `K : DerivedCategory (ModuleCat.{max u v} A)` and `hK : IsPseudoCoherent K`
  are the given pseudo-coherent derived object. The explicit
  `HasDerivedCategory.{w}` binder is the chosen localization universe, not an
  additional mathematical restriction. The coefficient universe `max u v`
  includes the ring and is closed under the stated module completions.
- `supportedExtFunctor K i` is the composite of the degree-zero single functor,
  shift by the arbitrary integer `i`, and the existing A-linear coyoneda
  functor at `K`. Thus its value is precisely `Hom(K,M[0][i])`, and its maps
  are postcomposition by the shifted coefficient morphisms. We use this
  existing categorical construction rather than define another Ext theory.
- The integer threshold is `a : ℤ`. The support hypothesis quantifies over
  EVERY `M : ModuleCat.{max u v} A` with `Module.Finite A M`, EVERY integer
  `i` with `a ≤ i`, and EVERY ideal `p` with `[p.IsPrime]` and `¬ I ≤ p`.
  `Subsingleton (LocalizedModule p.primeCompl ((supportedExtFunctor K i).obj M))`
  says exactly that the localization of the Ext module at p is zero. It does
  not say that the unlocalized Ext group is zero.
- The first conclusion quantifies over finite `N` and all integers `i ≥ a`
  and asserts `IsIso (supportedExtQuotientComparison I K i N)` in `ModuleCat A`.
  The helper `supportedExtCoefficientTower I N` has index n equal to
  `N/(I^(n+1) • ⊤)`, so the limit starts with power one as in the node.
  Its arrows are Mathlib's `AdicCompletion.transitionMap`, not chosen arrows.
  `supportedExtQuotientTower` applies the same Ext coefficient functor.
  `supportedExtQuotientCone` applies that functor to the cone of the actual
  quotient maps. `supportedExtQuotientComparison` is `limit.lift` of this
  cone. Therefore every projection is exactly the quotient-induced map.
- The second conclusion is `IsIso` of the same Ext functor applied to
  `supportedExtCompletionUnit I N`. This helper is exactly
  `AdicCompletion.of I N : N →ₗ[A] AdicCompletion I N` as a module morphism.
  No finiteness hypothesis is imposed on the completed module.
- The third conclusion gives the naturality square for the FIRST map after
  EACH `limit.π` at `op n`. The intervening coefficient morphism is
  `supportedExtQuotientMap I f n`, the existing `LinearMap.reduceModIdeal`
  restricted back to A. Equality in a limit is detected by its projections,
  so this is exactly naturality for the inverse-limit map, with no loss of
  information and without assuming arbitrary maps on limits.
- The fourth conclusion is the naturality square for the SECOND map, using
  `supportedExtCompletionMap I f`, which is `AdicCompletion.map I f.hom`
  restricted back to A. Both squares quantify over all morphisms between
  finite coefficient modules. All maps lie in `ModuleCat A`, hence are A-linear.

The eight helper declarations belong to the two canonical maps of this node
and are listed in `lean.declarations`. They are compositions, an indexed
quotient diagram, a cone and its universal map, or bundled existing linear
maps; none introduces an independent mathematical prerequisite. The small
proof in the cone definition only checks its structural compatibility with
quotient transitions, using definitional reduction and existing functor laws.

Statement dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, the Noetherian
  self-module condition, equivalent to finite generation of every ideal.
- `WeilConjectures.RingTheory.RingPseudoCoherent`:
  `DerivedCategory.IsPseudoCoherent`, a bounded-above finite free complex and
  an isomorphism of its image to K. This is the dependency's upstream twin.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory` and
  `HasDerivedCategory`, with `DerivedCategory.singleFunctor`.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`, finite generation of
  the top submodule.
- `Mathlib.Algebra.Module.LocalizedModule.Basic`: `LocalizedModule` at
  `p.primeCompl`.
- `Mathlib.RingTheory.AdicCompletion.Basic` (publicly supplied through
  `AdicCompletion.Functoriality`): `AdicCompletion`, `AdicCompletion.of`, and
  `AdicCompletion.transitionMap`. Its completion is compatible quotient
  sequences; omitting level zero changes nothing, since that quotient is zero.

Already stated proof dependencies are imported non-publicly from Mathlib:
`CochainComplex.isKProjective_of_projective`,
`CochainComplex.IsKProjective.Qh_map_bijective`, `Submodule.FG.of_le`,
`Module.mem_support_iff_of_finite` / `Module.support_eq_zeroLocus`,
`PrimeSpectrum.zeroLocus_eq_iff` / `Ideal.radical_eq_sInf`,
`Ideal.exists_pow_le_of_le_radical_of_fg`, and the three
`AdicCompletion.map_injective`, `.map_exact`, `.map_surjective` declarations.
The proof dependency `lem-sfb-finite-short-complex-adic-cohomology-limit` has
no Lean record in the read repository; there is no module to import yet. It
is retained unchanged in the DAG proof dependencies and named in the proof
docstring. It supplies no missing object in this statement.

Sources read: local Stacks `more-algebra.tex`, labels
`lemma-ext-annihilated-into` (0DYJ), `lemma-ext-induced-toplogy` (0DYI),
`lemma-base-change-RHom` (0A6A, case 3), and
`lemma-consequence-Artin-Rees` (0EGU). Also the latest blueprint
`sec-six-functors-basics/sk-thm-sf-ctf-stability/`
`sk-thm-sf-ctf-stability-direct-images.proof.md` for the item's inherited route.
0DYJ uses I-power torsion; for the finite Ext modules here this is equivalent
to the stated localization support hypothesis, by the support and radical
criteria already in the node's proof. The coefficient-completion clause
follows exact completion as the supplied proof explains.

Edge cases checked mathematically before finalizing:

- I = 0: all positive-power quotients are N and both maps are identities
  under the canonical identifications; the support condition is vacuous.
- I = A: every quotient and completion is zero; the support hypothesis forces
  each finite Ext group in the specified range to vanish.
- The zero ring, K = 0, and N = 0 give zero source and targets and are included.
- Negative i and arbitrary negative a are included by `ℤ`; no positive-degree
  or bounded-below condition on K was introduced. K may be unbounded below.
- No completeness, proper-ideal, Jacobson-ideal, or finiteness assumption on
  the completed coefficient module is present. The two module universes are
  not forced equal; neither is the derived morphism universe.
- All variables and universes are explicit; `set_option autoImplicit false`
  makes accidental auto-bound variables impossible.

Searches (all made before choosing the statement construction):

- `msearch.py ... leanfinder`:
  `Supported pseudo-coherent derived Hom groups commute with adic completion of finite coefficient modules`.
  Eight hits included `AdicCompletion.map_exact`, `.eval_comp_of`,
  `.ofTensorProductEquivOfFiniteNoetherian`, `.map_of`, and `.eval_of`.
  These provide ordinary completion tools, not the node's derived statement.
- `msearch.py ... leanfinder`:
  `Ext of pseudo-coherent complex commutes with completion supported finite modules`.
  Eight hits gave ordinary Ext, local cohomology diagrams, and Ext map laws;
  none states the supported pseudo-coherent completion comparison.
- `msearch.py ... loogle`: `"AdicCompletion", "Ext"`.
  Twelve hits were completion extensionality lemmas, not Ext comparison.
- `msearch.py ... grep`: `Ext.*completion|completion.*Ext` under
  `Algebra/Homology`. Only an unrelated idempotent-completion comment matched.
- `rg` in the project's `lean/WeilConjectures` and `lean/Sheaf` searched
  supported Ext, Ext/completion, the item's blueprint id, and the intended
  declaration names. No same statement was found. General completion and
  Koszul coefficient comparison modules do not say this statement.
- Direct Mathlib searches found `CategoryTheory.linearCoyoneda`,
  `DerivedCategory.singleFunctor` and its linearity instances,
  `Functor.ofOpSequence`, `NatTrans.ofOpSequence`, and module-category limits.
  These are used instead of new versions of those notions.

Validation: the module passed `scompile.py` against the live server within
60 seconds. A scoped heartbeat allowance covers elaboration of the four
clauses, while leaving the required wall-clock limit unchanged. Initial
local overlay attempts intermittently reported a full device; the wrapper's
normal server-confirmation fallback successfully compiled the module.

## Second reading by Q109

A separate pass through the node and the completed file checked the six
statement dependencies, every binder, both comparison constructions, and
each naturality square against the clause mapping above. In particular the
support condition uses Ext localized at a prime, the first tower begins at
power one, the second target uses ordinary completion of N, and naturality
of the first map is tested at every jointly detecting limit projection.
The first construction was simplified to map the ordinary quotient cone
through Ext, and explicit coefficient morphisms were named to avoid slow
elaboration; these changes do not change the statement. No mathematical
mismatch or statement correction was found. This is an in-process second
pass, not a claim of independent-agent review: the dispatcher explicitly
forbids starting other agents and assigns independent review to the maintainer.

## Delivery tool failure

The prescribed dry run passed and printed:
`OK (dry run): commit 873c48508d6 passes the preflight and compiles; nothing pushed`.
Three subsequent normal `deliver2.py Q109 lem-sfb-supported-complex-ext-completion`
attempts failed before pushing, each at the wrapper's compile step with
`resource exhausted (error code: 28, no space left on device)`.
The final retry followed a one-minute wait. No launcher script, shared file,
server temporary directory, or compilation gate was modified or bypassed.
The module, complete node record and report remain in the assigned sandbox.


## Resumed validation, 2026-10-24

The retained packet was inspected before the required first dry run. Against the
current read-only DAG, its only changed node field is `lean`; the stored theorem
signature matches the module verbatim. A fresh reading checked the upstream
`DerivedCategory.IsPseudoCoherent` definition, the recorded Mathlib notions,
the Stacks 0DYJ statement, and the current blueprint proof. Searches of both
`lean/WeilConjectures` and `lean/Sheaf` found no declaration with the item's
identifier or its delivered comparison names. The file still has exactly one
`sorry`, the assigned theorem, and the canonical-map definitions have real data.
No source or statement repair was indicated.

The resumed required `deliver2.py ... --no-push` failed during its server
compilation with `sandbox Sheaf.Stage2.Sandbox0` followed by
`resource exhausted (error code: 28, no space left on device)` (18.3 seconds).
A separate prescribed `scompile.py Q109 lem-sfb-supported-complex-ext-completion`
check of the delivered module failed with the identical message (18.3 seconds).
These are storage failures in the prescribed compilation infrastructure, not
Lean elaboration diagnostics. The packet is retained unchanged except for this
report. No shared source, launcher script, build artifact or server temporary
directory was edited, removed or bypassed.

The final `deliver2.py ... --no-push` retry also failed at server compilation
with the identical error 28 after 18.3 seconds; it explicitly printed
`nothing pushed`. Resumed attempts: two dry runs and one direct scompile check.

## Further dispatcher retry, 2026-10-24

Retained the saved module and node. The required initial `deliver2.py Q109
lem-sfb-supported-complex-ext-completion --no-push`, a direct prescribed
`scompile.py` of the saved module, and a final identical dry run each failed
on the server after 18.3 seconds with:

```
sandbox Sheaf.Stage2.Sandbox0
resource exhausted (error code: 28, no space left on device)
```

Both dry runs explicitly reported `nothing pushed`. This retry again checked
that only `lean` differs from the current read-only node, its recorded signature
matches the module verbatim, all six statement dependencies retain the recorded
interfaces, and the module has exactly one `sorry`. Current source searches
found no duplicate of the item's identifier or comparison declaration. There
was no Lean diagnostic to repair: all three attempts stopped at the same
storage failure in the prescribed compilation infrastructure. No launcher
script, shared source, build artifact, or server temporary directory was
modified or removed. The complete packet remains in this sandbox.

## Dispatcher retry after try 3, 2026-10-24

The saved report and packet were retained. The required initial dry run,
a direct `scompile.py Q109 lem-sfb-supported-complex-ext-completion
lean/Sheaf/RingTheory/SupportedComplexExtCompletion.lean`, and a final dry-run
retry all failed after 18.3 seconds with the same server diagnostic:

```
sandbox Sheaf.Stage2.Sandbox0
resource exhausted (error code: 28, no space left on device)
```

Both `deliver2.py ... --no-push` runs explicitly printed `nothing pushed`.
The current shared node and retained node still differ only in `lean`; the
recorded theorem signature matches the module verbatim and its sole `sorry`
is the assigned theorem. The six current statement-dependency records and
upstream pseudo-coherent definition were checked again. Searches in both
live source roots found no duplicate of the item or its comparison names.
No Lean diagnostic was emitted to repair. The module and node were unchanged;
only this retry record was appended. No launcher files, shared source or
server build/temporary files were edited, removed or bypassed.


## Dispatcher retry after try 4, 2026-10-24

Inspected the saved report and retained packet, then ran the required initial
`deliver2.py Q109 lem-sfb-supported-complex-ext-completion --no-push`.
It failed at server compilation after 18.3 seconds with error 28,
`resource exhausted (error code: 28, no space left on device)`, explicitly
reporting `nothing pushed`. A direct prescribed `scompile.py` check of
`lean/Sheaf/RingTheory/SupportedComplexExtCompletion.lean` failed with the
identical server diagnostic after 18.3 seconds.

The current shared node and retained node differ only in `lean`; the signature
matches the module verbatim, all lines fit 100 characters, and the assigned
theorem is its sole `sorry`. Read the current pseudo-coherent dependency and
checked all six statement-dependency records. Current searches of both Lean
source roots found no duplicate of the item or its comparison declarations.
No repair note exists for the item. No Lean diagnostic was emitted to repair.
The module and node remain unchanged; no launcher file, shared source, server
artifact or temporary directory was modified, removed or bypassed.

The final prescribed dry-run retry failed with the identical server error 28
after 18.3 seconds and explicitly reported `nothing pushed`. This retry made
two dry-run attempts and one direct compile attempt; the saved packet remains
ready for validation once the compilation infrastructure has storage available.

## Dispatcher retry after try 5, 2026-10-24

Inspected the saved report and module and ran the required initial
`deliver2.py Q109 lem-sfb-supported-complex-ext-completion --no-push`.
It failed during server compilation after 18.3 seconds with:

```
sandbox Sheaf.Stage2.Sandbox0
resource exhausted (error code: 28, no space left on device)
```

A direct prescribed `scompile.py` check of the saved module and a final
`deliver2.py ... --no-push` retry failed identically, each after 18.3 seconds.
Both dry runs explicitly printed `nothing pushed`. No Lean elaboration
error or warning was produced to repair.

The retained node differs from the current shared node only in `lean`; its
recorded signature occurs verbatim in the module. The module has exactly one
`sorry`, the assigned theorem, and no lines over 100 characters. Rechecked
all six statement-dependency records and the upstream pseudo-coherent
interface. Current searches in `lean/WeilConjectures` and `lean/Sheaf` found
no duplicate of the item or its comparison declarations. The unstated proof
helper still has no Lean record. No mathematical or source change was
indicated. The module and node are retained unchanged. No launcher script,
shared source, or server artifact/temporary directory was edited or removed.

## Dispatcher retry after try 6, 2026-10-24

Inspected the saved report and retained packet before running the required
initial `deliver2.py Q109 lem-sfb-supported-complex-ext-completion --no-push`.
That dry run, a direct prescribed `scompile.py` check of the saved module,
and a final identical dry-run retry all failed during server compilation
after 18.3 seconds with:

```
sandbox Sheaf.Stage2.Sandbox0
resource exhausted (error code: 28, no space left on device)
```

Both dry runs explicitly reported `nothing pushed`. There was no Lean
elaboration diagnostic to repair. The retained node still differs from the
current shared node only in `lean`, and the stored theorem signature matches
the module verbatim. Its only `sorry` is the assigned theorem; all lines fit
100 characters. Checked the six current statement-dependency records and
read the upstream pseudo-coherent definition and the recorded Mathlib
interfaces. Current searches of both project Lean source roots found no
duplicate identifier or comparison declaration; no repair note exists.
The Stacks 0DYJ statement still matches the report's source discussion.
No source change was indicated. The module and node remain unchanged;
only this retry record was appended to the report. No launcher file,
shared source, server artifact or temporary directory was modified,
removed or bypassed. The saved packet remains ready for validation when
the prescribed compilation infrastructure has storage available.

## Successful dispatcher retry, 2026-10-24

The required initial dry run now passed: `OK (dry run): commit 63fa3f1b44b
passes the preflight and compiles; nothing pushed`. Retained the saved module
and node without changes. The final self-check compared the current node's
hypotheses and all four conclusion clauses with the module, including the
canonical quotient cone, completion unit and both naturality squares. It
found no mismatch. The six statement-dependency records and their current
upstream/Mathlib interfaces still agree with the recorded translation.
The node differs from the current shared node only in `lean`; its signature
matches the module verbatim. The only `sorry` is the assigned theorem, all
lines fit 100 characters, and current searches of both project source roots
found no duplicate of the assigned statement or its helper names. No repair
note exists for this item. The earlier storage failures are historical;
the prescribed dry run now validates the retained packet successfully.
