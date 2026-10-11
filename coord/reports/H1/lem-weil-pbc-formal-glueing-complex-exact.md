## Worker report

The module `Sheaf.RingTheory.FormalGlueingComplexExact` states
`RingTheory.formalGlueingComplexExact`, with one sorry proof and no new definitions.
Source read: https://stacks.math.columbia.edu/tag/05EK, Lemma 15.91.9,
the second computational proof, together with the equation preceding it.
The local Stacks checkout is absent on this machine, so the official online source
was consulted. The node's eight proof steps are carried in the theorem docstring.

Hypotheses and clauses, matched individually:

- Commutative rings R and S: independent `R : Type u`, `S : Type v`,
  `[CommRing R]`, `[CommRing S]`; zero rings are admitted.
- The flat ring map φ: `(φ : R →+* S) (hflat : φ.Flat)`, using the recorded
  `RingHom.Flat`. The `letI : Algebra R S := φ.toAlgebra` gives exactly its
  scalar action for the tensor product; no second action is selected.
- A finite list of generators: `(t : ℕ) (f : Fin t → R)`, including the empty list.
  The ideal I is written in place as `Ideal.span (Set.range f)`; its extension IS
  is `(Ideal.span (Set.range f)).map φ`.
- The induced map R/I → S/IS is an isomorphism: `hquot` asserts
  `Function.Bijective (Ideal.quotientMap ... φ Ideal.le_comap_map)`. This is the
  induced map itself, not the existence of an arbitrary isomorphism of the quotient
  rings; bijectivity of a ring homomorphism is equivalent to being a ring isomorphism.
- Arbitrary R-module M: `(M : Type w) [AddCommGroup M] [Module R M]`, with its
  universe independent of both ring universes, with no finiteness condition.
- Scalar extension: `S ⊗[R] M`, the factor order of the recorded
  `def-weil-module-base-change`. `TensorProduct.comm R M S` identifies the node's
  `M ⊗[R] S` with this object and sends m⊗1 to 1⊗m; both are the same extension
  of scalars. The local linear map `η := TensorProduct.mk R S M 1` is m↦1⊗m.
- M_fi and M_fifj: `LocalizedModule.Away (f i) M` and
  `LocalizedModule.Away (f i * f j) M`; `(M ⊗ S)_fi` is
  `LocalizedModule.Away (f i) (S ⊗[R] M)`. These are the recorded localization.
- Canonical identification of localized scalar extension with extension of the
  localization: the theorem uses the localized map of η, `IsLocalizedModule.map`
  with the two `mkLinearMap` maps. It sends m/fᵢᵉ to (1⊗m)/fᵢᵉ; under the node's
  canonical tensor/localization identification this is exactly mᵢ⊗1. The node's
  proof step 2 expressly permits this rendering. No extra chosen identification or
  unconstrained map is added to the hypotheses.
- The middle object is `(S ⊗[R] M) × (∀ i : Fin t, M_fi)` in the type of α and β.
  The final object is the product of `(∀ i, (S ⊗[R] M)_fi)` and
  `(∀ i j, M_fifj)`; all ordered pairs are present, including i=j.
- α(m)=(m⊗1,(m/1)i): the `let α` pairs `η m` with each `mkLinearMap ... M m`.
- The first β component is m'/1 − mᵢ⊗1: the first lambda in `let β` subtracts
  `IsLocalizedModule.map ... η (p.2 i)` from `mkLinearMap ... p.1`.
- The second β component is mᵢ/1 − mⱼ/1 in M_fifj: the second lambda in β
  subtracts the two `ρ` maps. `ρ a h ha` is the recorded `IsLocalizedModule.lift`
  of M→M_h across M→M_a. `localizationAway_map_units_of_dvd` supplies invertibility,
  and the two divisibility witnesses are `dvd_mul_right` and `dvd_mul_left`.
  `IsLocalizedModule.lift_apply` characterizes both maps by m/1↦m/1; hence they
  have exactly the fraction formula gᵉm/(fg)ᵉ of the localization dependency.
- Exactness at M: `Function.Injective α` renders the initial 0→M term.
- Exactness in the middle: `Function.Exact α β` says precisely that β(p)=0 iff
  p=α(m) for some m, i.e. Ker β=Im α. Both directions, including βα=0, are included.
  The maps are written as functions with explicit formulas; they are the underlying
  functions of the canonical R-linear maps, and the exactness notion uses no weaker
  or stronger condition than the node's last sentence.

Dependency declarations read and used:

- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`, whose definition is
  `Module.Flat R S` using `φ.toAlgebra` (the flat-map dependency).
- `Mathlib.LinearAlgebra.TensorProduct.Tower`: recorded scalar-extension notion
  `TensorProduct`, `TensorProduct.mk`; the recorded `LinearMap.baseChange` signature
  and docstring were read. No base change of a linear map is needed here, so
  `LinearMap.baseChange` itself is not applied.
- `Mathlib.Algebra.Module.LocalizedModule.Basic` (available through the landed
  import): `LocalizedModule.Away`, `LocalizedModule.mkLinearMap`,
  `IsLocalizedModule.lift`, and `IsLocalizedModule.map`; the full declarations,
  docstrings and their fraction/map-compatibility lemmas were read.
- `Sheaf.RingTheory.CoverModuleExact`: `RingTheory.localizationAway_map_units_of_dvd`.
  Its docstring and full signature were read. The landed node
  `lem-weil-pbc-cover-module-exact` was added to stmt_deps solely to cite this
  already existing helper; its unit-ideal Cech exactness theorem is not used and
  its unit-ideal hypothesis is not imposed here. No dependency module is rewritten.
- `Mathlib.RingTheory.Ideal.Quotient.Operations`: `Ideal.quotientMap` is the
  canonical induced quotient map, with `Ideal.le_comap_map` its well-definedness.

Edge cases checked mathematically before writing: t=0 gives I=0 and forces φ to
be an isomorphism, so α is scalar extension with terminal empty product and β has
zero target; the asserted exactness follows. A zero generator gives a zero
localization; repeated generators and the diagonal i=j cause no change (the two
canonical overlap maps coincide on the diagonal). I=R makes the quotient condition
vacuous but the localizations cover Spec R, giving the ordinary Cech gluing
statement even when φ is not faithfully flat. φ=id is allowed, the zero module
is allowed, and zero rings force the corresponding modules to be zero. No
Noetherian, nonzero-ring, positive-t, or faithful-flatness restriction occurs.

Searches made on 2026-10-11:

- msearch.py leanfinder, query `exactness of formal glueing complex for a flat ring
  map inducing isomorphism modulo a finitely generated ideal`: eight results,
  including `Module.FaithfullyFlat.range_le_ker_of_exact_rTensor`,
  `Module.FaithfullyFlat.lTensor_exact_iff_exact` and cotangent-complex exactness;
  none states this formal glueing sequence.
- msearch.py loogle, query `LocalizedModule.mkLinearMap, IsLocalizedModule.map`:
  five results including `IsLocalizedModule.map_LocalizedModules`,
  `IsLocalizedModule.map_iso_commute`, `LocalizedModule.map_exact`; these provide
  localization tools, not the item.
- msearch.py grep, query `formal[Gg]lu|glueing|Beauville`, subdirectory RingTheory:
  zero hits in Mathlib.
- msearch.py leansearch, query `formal glueing exact sequence of modules for flat
  ring homomorphism isomorphism modulo ideal`: service unavailable (HTTP internal
  server error); no mathematical absence conclusion is drawn from that search.
- rg in WeilConjectures for `formal glue|formalGlue|Beauville|laszlo` and for the
  item id: no matching item statement. rg in lean/Sheaf found `FormalGlueingData`
  (data and canonical maps, not exactness) and `CoverModuleExact` (unit-ideal
  covering, not flat formal glueing); the latter's existing helper is reused.
- rg for the proposed name `formalGlueingComplexExact` in Mathlib,
  WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json: no existing name.

No statement correction, new definition node, hollow definition, or disputed
statement is needed. Server scompile.py: compiled cleanly in 1.8 seconds.

## Second reading by H1

I independently read the sandbox node and all eight proof steps, the complete
Lean module, all four statement-dependency nodes and their recorded declarations,
and the Stacks TeX at `section-formal-glueing`, `equation-glueing-complex` and
`lemma-recover-module-from-glueing-data` (tag 05EK). The local literature checkout
is absent; I fetched the official stacks/stacks-project `more-algebra.tex` into
this item's scratchpad and also checked the official tag page. The section's
opening Noetherian scheme is motivation for the later application, not a
hypothesis on the rings in this self-contained algebra lemma. The lemma requires
only flatness, finitely many generators, and the induced quotient isomorphism.
The TeX's malformed overlap formula is already addressed by the reviewed node:
the target has all pairs and the computational proof requires all pairwise
compatibilities. No new correction is needed.

My object/hypothesis/conclusion checklist and matching Lean:

1. Commutative rings R and S and a specified map: `{R : Type u} {S : Type v}`,
   `[CommRing R] [CommRing S]`, `(φ : R →+* S)`. Exact match; neither ring is
   required to be nonzero, a domain, a field, or Noetherian.
2. Flatness of that map: `(hflat : φ.Flat)`. I opened `RingHom.Flat`: it is
   `Module.Flat R S` for `φ.toAlgebra`. The theorem's local `letI` uses that same
   algebra, with no additional algebra or flatness assumption. Match.
3. Finite list and its generated ideal: `(t : ℕ) (f : Fin t → R)` and
   `Ideal.span (Set.range f)`. Every finite list, including empty, is represented.
   The extension ideal is exactly `(Ideal.span (Set.range f)).map φ`. Match.
4. The induced quotient map is an isomorphism: `hquot : Function.Bijective
   (Ideal.quotientMap ... φ Ideal.le_comap_map)`. I read `Ideal.quotientMap`
   and `quotientMap_mk`: its domain is R modulo that span and its value at [r]
   is [φ r]. Bijectivity of this ring homomorphism is exactly the required
   isomorphism condition, not an unrelated isomorphism between quotients. Match.
5. An arbitrary R-module: `(M : Type w) [AddCommGroup M] [Module R M]`.
   No finite generation or torsion condition is assumed. Match.
6. Base change and its canonical map: `S ⊗[R] M` and
   `η := TensorProduct.mk R S M 1`. I read the recorded `LinearMap.baseChange`
   and the tensor `mk` and `comm` signatures/formulas. The dependency explicitly
   uses this factor order; `TensorProduct.comm` sends the node's m⊗1 to 1⊗m.
   Thus these are precisely the node's base change and canonical map. Match.
7. Principal localizations M_fi, M_fifj and (M⊗S)_fi:
   `LocalizedModule.Away (f i) M`, `LocalizedModule.Away (f i * f j) M`,
   and `LocalizedModule.Away (f i) (S ⊗[R] M)`. I read `Away` and
   `mkLinearMap` in the dependency module: these localize at powers and send
   m to m/1. Match.
8. Canonical identification in the first β component: `IsLocalizedModule.map`
   applied to η and the two localization maps. Its `map_mk'` formula is
   x/f^e ↦ (1⊗x)/f^e; this is m_i⊗1 under the canonical identification in the
   node (also explicitly explained in node proof step 2). No arbitrary comparison
   map or extra condition is used. Match.
9. Canonical overlap maps: local `ρ` uses `IsLocalizedModule.lift`; I read its
   signature, `lift_apply` and `lift_unique`. The imported
   `localizationAway_map_units_of_dvd` requires only divisibility, not a cover.
   The two witnesses `dvd_mul_right` and `dvd_mul_left` therefore give the
   unique maps M_fi → M_fifj and M_fj → M_fifj sending m/1 to m/1.
   Their fraction formulas are f_j^e m/(f_i f_j)^e and f_i^e m/(f_i f_j)^e.
   This reuses the recorded localization notion, not a private replacement. Match.
10. The middle object is `(S ⊗[R] M) × (∀ i : Fin t, ... M)`;
    the last object is `(∀ i : Fin t, ... (S ⊗[R] M)) × (∀ i j : Fin t, ... M)`.
    These are exactly the finite products specified, with all ordered pairs. Match.
11. α: `fun m ↦ (η m, fun i ↦ mkLinearMap ... M m)` gives both required
    components. β's first lambda is m'/1 minus localized η of m_i, and its
    second is `ρ ... (p.2 i) - ρ ... (p.2 j)`. Both signs and every index agree.
    Match.
12. Injectivity and middle exactness: `Function.Injective α ∧ Function.Exact α β`.
    I read Mathlib's additive exactness definition (generated from `MulExact` in
    `Algebra/Exact/Basic.lean`): for every p, β p = 0 iff p ∈ Set.range α.
    This is precisely Ker β = Im α, including β∘α=0, together with the initial
    injectivity clause. The formulas are underlying functions of linear maps;
    no linearity assumption or conclusion has been lost. Match.

Edge cases: t=0 gives I=0 and hquot forces φ itself to be an isomorphism;
α is then bijective onto scalar extension times the empty product and β's
codomain is zero. A zero generator has zero localization; repeated generators
and i=j are included (the diagonal difference is zero). I=R is allowed: the
quotient condition is then automatic and the localizations supply the cover.
M=0, zero rings, φ=id, nilpotents and every characteristic are admitted.
R, S and M have independent universes u, v, w; the tensor and localization
carriers use the necessary maxima automatically. There are no schemes or
independent positive integer parameters to restrict; the empty affine scheme
corresponds to the allowed zero ring. In using the docstring proof one may
choose a positive common denominator exponent, as in the source, and handle
t=0 separately as its last sentence does.

Independent searches (2026-10-11; recorded also in searches.jsonl):

- LeanFinder: `recover module from scalar extension and principal localizations
  equalizer flat quotient isomorphism`. Eight flatness/localization results,
  including `Module.flat_of_isLocalized_span`; none states this equalizer.
- Loogle: `Function.Exact, LocalizedModule`. Results
  `exact_of_localized_maximal`, `exact_of_localized_span`, and
  `LocalizedModule.map_exact` are local tests/preservation of an already given
  exact sequence, not the present sequence or its quotient hypothesis.
- LeanSearch: `module recovered by equalizer of scalar extension and finitely
  many localizations under flat quotient isomorphism`; unavailable (HTTP internal
  server error), recorded without drawing an absence conclusion.
- Mathlib grep: `patching|equalizer|recover` in RingTheory. Generic flat
  equalizer preservation and ring tensor equalizers occur, not this module
  recovery statement. Direct rg for patching, formal glueing, Beauville and
  Laszlo in WeilConjectures, Mathlib RingTheory and lean/Sheaf found only the
  project's formal glueing data module. I opened it: its objects, comparisons
  and compatibility lemmas do not assert this exactness. The already-read
  CoverModuleExact theorem requires the unit ideal and is a different statement.
  The proposed declaration name is absent from Mathlib/project upstream names.

There are no new definition nodes or dependency modules to review. The one
added landed dependency supplies only the invertibility helper, and does not
impose its cover theorem's stronger hypothesis. No statement correction record
is present or needed. No mismatch was found and no Lean or node text was
changed. I preserved the worker report and appended this independent review.
The theorem has exactly one `sorry` proof; the local abbreviations have concrete
data and no hollow definitions. Module and theorem docstrings cite the source
and blueprint id, and all eight proof steps are present. The explicit u/v/w and
binders leave no variable unbound. The node's `lean.statement` equals the file's
signature verbatim. Server scompile.py compiled the reviewed file cleanly in
1.8 seconds, exit 0, with no warnings.
