## Worker report

Module: `lean/Sheaf/AlgebraicGeometry/FormalModuleSupportConstant.lean`.
Declaration: `AlgebraicGeometry.formalModule_support_eq`. It states constant support
of all positive levels of a coherent formal module, with its sole proof `sorry`.
No definitions, extra nodes, dependency modules, or statement corrections are needed.

Hypothesis and clause correspondence:
- A Noetherian scheme X is `{X : Scheme.{u}} [IsNoetherian X]`.
  Mathlib's class extends precisely `IsLocallyNoetherian X` and `CompactSpace X`,
  the node's locally Noetherian and quasi-compact assumptions.
- The quasi-coherent ideal sheaf I is `(I : X.IdealSheafData)`, exactly the
  representation used by the recorded coherent-formal-module dependency.
- An object of Coh(X,I) is `(F : CoherentFormalModule X I)`. Its underlying
  inverse-system functor is `F.obj`, and `F.obj.obj (op n)` is level n+1.
  The full-subcategory property supplies coherence, annihilation by I^(n+1),
  and the quotient isomorphism induced by the transition map.
- Every positive level is `(n : ℕ)` with this shift: the natural numbers
  bijectively enumerate the node's levels 1,2,... . In particular `op 0`
  represents F_1; no level-zero module is assumed or discarded.
- The support of F_(n+1) is
  `{x : X | ¬ Subsingleton ((F.obj.obj (op n)).presheaf.stalk x)}`.
  The corresponding right-hand set uses `op 0`. An abelian-group stalk is
  zero exactly when its underlying type is subsingleton, so these are precisely
  the nonzero-stalk loci, and the conclusion is equality of these sets.

Dependencies inspected and used:
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`
  and `AlgebraicGeometry.IsNoetherian`; read their signatures and docstrings.
- `Sheaf.AlgebraicGeometry.CoherentFormalModule`:
  `AlgebraicGeometry.CoherentFormalModule`, including the full definition of
  `IsCoherentFormalModule`, its quotient condition, and the level-index convention.
  This is the sole direct import and supplies the other required imports transitively.
- `Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase`:
  `AlgebraicGeometry.Scheme.Modules.HasSupportProperOver` and its docstring give
  the shared inline support encoding for clause (2) of that dependency. There
  is no standalone support declaration to call; the inline convention is followed,
  without adding a properness hypothesis or a base scheme.

Source: the repository does not contain `literature/stacks-project/coherent.tex`
on this machine, so the cited source was opened at
https://stacks.math.columbia.edu/tag/0CYV . The first sentence in the proof of (1)
asserts precisely the equality used here. The node isolates this equality from
its surrounding proper-support assertion; the equality requires no base morphism.
The theorem docstring carries all three proof steps and their dependency ids.

Edge cases checked: n=0 is exactly the level-one equality. The empty scheme
makes both sets empty. The zero formal system also has empty supports. The
zero ideal permits constant systems; the unit ideal forces zero levels.
The elementary stalk argument M=a^k M=a^(2k) M=0 works for k>=1,
including k=1, and needs no finiteness or Nakayama hypothesis. Universe u is
explicit and arbitrary, with no independent index-universe restriction.
No statement fault or STATEMENT-DISPUTED flag was found.

Searches for an existing statement:
- `msearch.py leansearch`, query `support of coherent formal module is independent
  of level`: service unavailable (Internal Server Error); no verdict assigned.
- `msearch.py leanfinder`, query `All levels of an inverse system of coherent
  sheaves modulo powers of an ideal have equal support`: eight hits, including
  `Module.support_quotient` and local-cohomology constructions. These concern
  ring modules, not the stated coherent sheaf inverse system; no exact match.
- `msearch.py loogle`, query
  `Module.support_quotient, AlgebraicGeometry.CoherentFormalModule`: zero hits;
  the latter identifier is unknown to the service.
- `msearch.py grep`, query
  `support.*[Ff]ormal|[Ff]ormal.*support|CoherentFormalModule` in
  `Mathlib/AlgebraicGeometry`: zero hits.
- `rg -n 'formal.*support|support.*formal|lem-weil-pbc-formal-system-support-constant'`
  in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and project `lean/Sheaf`:
  only unrelated formalism comments upstream and proper-support/completion
  definitions in `CoherentFormalModule.lean`; no constant-support theorem.
- `rg` for the item id and `formalModule_support_eq` in
  `dag/lean_names_upstream.json` and upstream `WeilConjectures`: no hits.

Validation: `scompile.py S1 lem-weil-pbc-formal-system-support-constant` on the
module completed with exit code 0 in 2.6 seconds, with no errors or warnings.

## Second reading by S1

Read the item node and delivered module together, independently of the worker's
correspondence. No mathematical or signature mismatch was found; the Lean and node
record are unchanged. This reading adds only this report and independent searches.

Object, hypothesis, and conclusion inventory and verdicts:
- Scheme X: `{X : Scheme.{u}}` introduces exactly the arbitrary scheme of the node.
  Universe `u` is declared explicitly. Verdict: matches.
- Locally Noetherian and quasi-compact X: `[IsNoetherian X]` extends precisely
  `IsLocallyNoetherian X` and `CompactSpace X` in Mathlib Noetherian. Read
  `isLocallyNoetherian_iff_of_affine_openCover` as well: its every-affine condition
  agrees with pqf-def-locnoeth's existence of a Noetherian affine cover. Compactness
  here is quasi-compactness, without a Hausdorff condition. Verdict: matches.
- Quasi-coherent ideal I of O_X: `(I : X.IdealSheafData)`. Read its affine-ideal
  fields and basic-open localization compatibility in Mathlib IdealSheaf.Basic,
  and its use through `I.toModulesι` in the recorded formal-module definition.
  It imposes no extra properness, radicality, or choice of base. Verdict: matches.
- Object (F_k) of Coh(X,I): `(F : CoherentFormalModule X I)`. Read the recorded
  dependency node and its actual abbreviation, `IsCoherentFormalModule`, and
  `formalModuleQuotient`. The full-subcategory property requires coherent levels,
  I^(n+1) F_(n+1)=0, and the transition-induced quotient isomorphism; the
  quotient is the cokernel of the shared ideal-product inclusion. Read the
  imported `RingedSpace.IsCoherent` definition: finite type and finite-type
  kernels for maps from finite free modules. No hidden stronger assumption.
  Verdict: matches the source category, with level shifted by one.
- Every positive level k: `(n : ℕ)` and `F.obj.obj (op n)` represent k=n+1.
  These enumerate all and only k>=1. Verdict: matches, including k=1.
- Support: the left set is
  `{x : X | ¬ Subsingleton ((F.obj.obj (op n)).presheaf.stalk x)}`;
  the right set is the same expression at `op 0`, hence F_1. Read the support
  dependency node clause (2) and `Scheme.Modules.HasSupportProperOver` in
  ClosedSubsetProperOverBase. It uses exactly this inline nonzero-stalk locus.
  For an additive module stalk, being zero means its carrier is subsingleton.
  The conclusion is equality of subsets, not mere inclusion or equality of
  closures. Verdict: matches the single conclusion clause and its quantifiers.

Source check: local Stacks TeX is absent. Independently read the upstream
`coherent.tex` at
https://raw.githubusercontent.com/stacks/stacks-project/master/coherent.tex,
lines 6256-6266 (section-coherent-formal), 7531-7545 (lemma-systems-with-proper-support),
and 7558-7567 (proof of (1)); also read https://stacks.math.columbia.edu/tag/0CYV
and https://stacks.math.columbia.edu/tag/0EHN. The surrounding lemma has a finite
 type map to a Noetherian base, which makes X Noetherian. Its support equality
is the assertion extracted by this node, and uses only the defining annihilation
and quotient conditions of Coh(X,I). No base object or proper-support hypothesis
belongs to this extracted assertion. The docstring follows the node's three steps:
stalk quotient and nilpotent annihilation, iterated ideal multiplication forcing
vanishing, then equality of nonzero-stalk loci and induction. All cited proof
nodes are named. The elementary implication uses 2k>=k+1 for k>=1.

Edge cases: Lean n=0 is the tautological F_1 equality, not an extra level F_0.
The empty scheme yields empty subsets; the zero system yields zero stalks and
empty supports. For I=0 the quotient conditions allow constant coherent systems;
for I=O_X annihilation forces zero levels. No field, characteristic, separatedness,
nonemptiness, or extra finiteness instance is assumed. There is no variable index
set to exclude; the index is exactly all positive integers. The arbitrary scheme
universe u and the shared module universe introduce no additional restriction.

Independent searches (different wording from the first reader):
- msearch.py leanfinder: `Nonzero stalk loci agree for successive nilpotent ideal
  quotients of an adic coherent sheaf system`: eight hits on local cohomology,
  adic-completion elements, and a structure-sheaf germ lemma; no formal-system
  support equality.
- msearch.py loogle: `Module.support_quotient`: one ring-module theorem, opened
  signature requiring Module.Finite and computing support on PrimeSpectrum.
  It is not the sheaf inverse-system theorem being delivered.
- msearch.py grep: `adic.*support|support.*adic|stalk.*quotient` in Mathlib
  AlgebraicGeometry: structure-sheaf quotient/germ and ideal-support hits only.
- rg in upstream WeilConjectures and project lean/Sheaf for `support_eq` and
  support with adic/completion/inverse: unrelated Weil-sheaf, divisor and
  compact-support results, plus formalCompletion_support_subset/proper. Those
  last declarations compare a module and its completion quotient or preserve
  properness, not equality between levels of an arbitrary formal system.
- rg for the item id and `formalModule_support_eq` in dag/lean_names_upstream.json
  and upstream WeilConjectures: no matches.
The worker's recorded LeanSearch attempt was unavailable; no conclusion is drawn
from it. The successful independent semantic, type-pattern, and local searches
find no existing exact statement. No new notion or dependency module is needed.

H5-H9: the delivery declares only one theorem with `by sorry`, no definitions,
private copies, proofs, local notation, or local instances. Its used import supplies
the shared formal-module category. Module and theorem docstrings have the source
and blueprint id; all variables and universe are bound. The node's lean.statement
is verbatim the delivered signature. No statement correction or disputed flag.
Validation: scompile.py was run on the absolute sandbox module path; clean compile.
