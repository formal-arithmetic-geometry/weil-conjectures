## Worker report

The module `Sheaf.AlgebraicGeometry.CoherentSupportPowerIdealKills` states
`AlgebraicGeometry.Scheme.coherent_support_power_ideal_kills`; its sole proof is `sorry`.
No definitions, dependency modules, new nodes, or statement corrections are needed.

Hypothesis and clause correspondence:
- The scheme is `(X : Scheme.{u})`, with explicitly bound universe `u`.
- Noetherian means `[IsNoetherian X]`: Mathlib defines this as locally Noetherian and
  compact underlying space, exactly the two conditions in the node.
- The O_X-module is `(F : X.Modules)`; coherence is the explicit hypothesis
  `(hF : RingedSpace.IsCoherent X.toRingedSpace F)`.
- The quasi-coherent ideal sheaf is `(K : X.IdealSheafData)`. Its actual module and
  inclusion are `K.toModules` and `K.toModulesι`, not an arbitrary morphism or ideal.
- The product K^t F is `idealModuleProduct (idealSheafPower K.toModulesι t).2 F`, using
  the shared image-of-multiplication construction. For positive exponents the recursive
  powers start with K and multiply by K. At zero the power is O_X with identity inclusion;
  the image of its multiplication is canonically F, so the node's zero-power convention
  is respected without a new definition.
- Vanishing is categorical `IsZero` of that product; the existential `∃ t : ℕ` includes
  all nonnegative exponents, including zero.
- Support is exactly the shared inline nonzero-stalk locus
  `{x : X | ¬ Subsingleton (F.presheaf.stalk x)}`.
- V(K) is exactly the non-surjective-stalk-inclusion locus of
  `RingedSpace.moduleStalkFunctor X.toRingedSpace x` applied to `K.toModulesι`.
  The recorded zero-set dependency uses this very expression: its injectivity clause
  identifies the stalk ideal with its image, and failure of surjectivity says this ideal
  is not the whole stalk ring. Its affine and closed-image clauses supply precisely the
  explanatory affine description and closed-subscheme identification in the node.
- `↔` joins existence of a killing power and `⊆` containment in that zero set. No extra
  closedness, affine equalities, or injectivity conclusions are added; those are the
  previously recorded dependency's description of the set, not additional conclusions
  of this lemma.

Dependency declarations read and used:
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian` and
  `AlgebraicGeometry.IsNoetherian` (through `Sheaf.AlgebraicGeometry.CoherentFormalModule`).
- `Sheaf.AlgebraicGeometry.Coherent`: `AlgebraicGeometry.RingedSpace.IsCoherent`.
- `Sheaf.AlgebraicGeometry.CoherentFormalModule` records the shared products and powers
  of `Sheaf.AlgebraicGeometry.IdealModuleProductStalk`:
  `AlgebraicGeometry.Scheme.idealModuleProduct`, `.idealSheafPower`.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`: `Scheme.IdealSheafData`, `Scheme.Hom.ker`.
  The source bridge `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module` supplies
  `Scheme.IdealSheafData.toModules` and `.toModulesι`.
- `Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase`: its support convention is used
  inline; its proper-over-base predicates do not apply to this statement.
- `Sheaf.AlgebraicGeometry.QuasiCoherentIdealZeroSetAffine`:
  `Scheme.quasi_coherent_ideal_zero_set_affine`, whose exact set expression is used.
  The imported `Sheaf.Algebra.Homology.ModuleStalkFunctor` supplies
  `RingedSpace.moduleStalkFunctor` for the stalk map.
Both direct imports provide notions appearing in the signature; no auxiliary local
notation, instance, private copy, or auto-bound implicit is used.

Edge cases checked mathematically before writing:
- Empty X: containment is vacuous and every sheaf is zero; t=0 works.
- Zero F: empty support and zero product for every t, including zero.
- K=0: V(K)=X and t=1 kills F.
- K=O_X: V(K) is empty and every power product is F; both sides hold exactly for F=0.
- t=0: the unit multiplication has image isomorphic to F; killing at zero means F=0.
- Arbitrary characteristic and scheme universe are allowed. No field, separatedness,
  properness, nonemptiness, or positive-exponent hypothesis is imposed.

Source checked: https://stacks.math.columbia.edu/tag/01Y9 (Lemma 30.10.2), which states
this equivalence and reduces it to Algebra 00L6 on a finite Noetherian affine cover.
The local `literature/stacks-project/coherent.tex` is unavailable on this machine, so
its official tag page was opened. The declaration docstring carries all seven proof
steps of the DAG, including their dependency names and the empty-cover case.

Searches for an existing statement (2026-10-11):
- `msearch.py ... leanfinder "coherent sheaf on a Noetherian scheme support contained in
  vanishing set of ideal iff killed by a power of ideal"`: eight hits, all ideal-sheaf
  support and zero-locus constructors/lemmas; no coherent-module killing equivalence.
- `msearch.py ... loogle "AlgebraicGeometry.Scheme.IdealSheafData, IsNoetherian"`:
  zero hits.
- `msearch.py ... leansearch "coherent sheaf support vanishing ideal power annihilation"`:
  unavailable (Internal Server Error); recorded as unavailable, without a verdict.
- `msearch.py ... grep "coherent.*support|support.*annihilat|power.*kills"
  AlgebraicGeometry`: zero Mathlib hits.
- `rg` on `WeilConjectures` and `lean/Sheaf` for coherent/support and support/ideal:
  related statements and proof references only; the source ideal-power results concern
  two ideal sheaves, not a general coherent module.
- Exact item-id search of `WeilConjectures`: no hits. Exact proposed declaration-name
  search in Mathlib, WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json: no hits.

No statement dispute or dependency fault was found. Server compilation and the delivery
preflight are run for this file; the independent second reading remains for the dispatcher.

## Second reading by P1

I independently opened the node, its seven proof steps, the proposed module, all six
statement-dependency node records, and the declarations below. No mathematical mismatch
was found; the Lean module and node are unchanged.

Object/hypothesis/conclusion checklist (H3):
- X is a scheme: `(X : Scheme.{u})`; pass. The explicit `universe u` is bound.
- X is locally Noetherian with quasi-compact underlying space: `[IsNoetherian X]`;
  pass. In Mathlib/AlgebraicGeometry/Noetherian.lean the class extends exactly
  `IsLocallyNoetherian X` and `CompactSpace X`. The former requires Noetherian
  section rings on affine opens, equivalent to the cover formulation of pqf-def-locnoeth.
- F is an O_X-module: `(F : X.Modules)`; pass. This is the sheaf-of-modules carrier
  accepted by the recorded coherence declaration, not a quasi-coherent-only category.
- F is coherent: `(hF : RingedSpace.IsCoherent X.toRingedSpace F)`; pass.
  I opened Coherent.lean: this is finite type together with finite-type kernels of
  every map from a finite free module on every open, exactly pqf-def-coherent.
- K is a quasi-coherent ideal subsheaf of O_X: `(K : X.IdealSheafData)`; pass.
  I read the compatible affine ideals in Mathlib's structure and the source bridge
  WeilConjectures/Mathlib/AlgebraicGeometry/IdealSheaf/Module.lean: `toModules`
  is the kernel of the structure-sheaf map to the closed-subscheme pushforward;
  `toModulesι` is its kernel inclusion. Thus this is an actual ideal, not an
  arbitrary module map. The closed-immersion dependency records `Scheme.Hom.ker`.
- K^t F for t >= 1: `idealModuleProduct (idealSheafPower K.toModulesι t).2 F`;
  pass. CoherentFormalModule.lean imports the shared IdealModuleProductStalk.lean,
  whose definitions I read: product is the image of tensor multiplication, power
  one is K and power n+2 is K times power n+1 with composed inclusion.
- K^0 F = F: the same expression at t=0; pass. The power definition returns
  the structure sheaf with identity inclusion, so the multiplication is the left
  unitor and its image is canonically F. No literal chosen-object equality is needed
  to express vanishing.
- Some nonnegative exponent kills F: `∃ t : ℕ, IsZero (...)`; pass. This is
  categorical zero in X.Modules, not `IsZero` on a bare type. No positivity is imposed.
- Supp(F): `{x : X | ¬ Subsingleton (F.presheaf.stalk x)}`; pass. I checked the
  inline convention in ClosedSubsetProperOverBase.lean against dependency part (2).
  No base morphism or properness hypothesis from unrelated parts is added.
- V(K): the set where `(RingedSpace.moduleStalkFunctor X.toRingedSpace x).map
  K.toModulesι` has a nonsurjective underlying linear map; pass. I opened the
  module-stalk functor and QuasiCoherentIdealZeroSetAffine.lean. The latter records
  stalk injectivity, the affine prime-ideal criterion, closedness, and equality with
  the image of the closed subscheme. Nonsurjectivity is precisely proper stalk ideal.
  These parenthetical identifications describe V(K), rather than new conclusions.
- Equivalence and containment: `(...) ↔ {x | ...} ⊆ {x | ...}`; pass. The
  existential is confined to the left side, with X, F, hF, K universally bound first.
  There are no omitted clauses or additional hypotheses.

Source: I retrieved the official Stacks source coherent.tex into the sandbox scratchpad
from https://raw.githubusercontent.com/stacks/stacks-project/master/coherent.tex and
read the section introduction and lines 2568-2582 (lemma-power-ideal-kills-sheaf).
It assumes exactly Noetherian X, coherent F, and a quasi-coherent ideal defining Z,
with a nonnegative killing exponent iff support lies set-theoretically in Z.
The official page https://stacks.math.columbia.edu/tag/01Y9 agrees. The section
introduces no extra base, separation, characteristic or finiteness assumptions.

Edge cases: empty scheme/empty affine cover allows t=0; zero F has empty support and
zero products; K=0 has V(K)=X and t=1 kills; K=O_X has empty zero set and the equivalence
reduces to F=0. At t=0 the product vanishes exactly when F does. There is no index
binder to exclude an empty index set. Arbitrary characteristic and arbitrary scheme
universe u are covered; no test-object quantifier or independent smaller universe occurs.

Independent H4 searches (different wording from the author):
- msearch leanfinder `nilpotent ideal action on coherent sheaf equivalent to stalk
  support inclusion`: eight hits, comprising ideal-support constructors, nilpotent
  structure-sheaf sections, reduced stalks, and germ lemmas; no matching theorem.
- msearch loogle `AlgebraicGeometry.Scheme.Modules, IsZero`: reports unknown identifier
  IsZero, so this query is inconclusive and is not evidence of absence.
- msearch leansearch `coherent module annihilation ideal power support containment`:
  unavailable (Internal Server Error), recorded without an absence verdict.
- Independent rg for `annihilat|nilpotent|support.*pow|pow.*support` in Mathlib's
  AlgebraicGeometry, the source's AlgebraicGeometry, and project AlgebraicGeometry:
  matches include Scheme.exists_pow_eq_zero_of_isNilpotent (structure-sheaf sections),
  IdealSheafData.support_pow (ideal zero sets), perfect-complex annihilation statements,
  and references to this node; none states this coherent-module equivalence.
  The existing product/power definitions and stalk functor are reused, not duplicated.

H5-H9: one theorem, proof solely `sorry`; no new definitions, dependency modules,
new nodes, private notions, local notation or instances. Both imports supply signature
notions. The docstrings identify 01Y9/00L6 and the blueprint node, and the proof
has all seven DAG steps, including local finite generation, affine product sections,
vanishing on the cover, affine support and zero set, the radical argument, and the
uniform maximum with the empty-cover case. No statement correction is present or needed.
I checked the node's lean.statement is verbatim the file signature and inspected all
binders. scompile.py compiled the delivered module cleanly in 2.6 seconds, exit 0.
Changes in this reading: only this independent report section; no Lean or node changes.
