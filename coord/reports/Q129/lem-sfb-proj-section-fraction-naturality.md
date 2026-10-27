## Worker report

The module `Sheaf.AlgebraicGeometry.ProjSectionFractionNaturality` states
`AlgebraicGeometry.Proj.projSectionFractionNaturality`, with proof `sorry`.
`IsProjSectionFractionNaturality` packages its canonical fraction equations; it is a
Prop-valued interface, not a replacement construction of twists, sheaves or localizations.

Source read: literature/stacks-project/constructions.tex, lemma-comparison-proj-quasi-coherent
(Tag 0B5I), including its displayed map and omitted gluing verification. The node expands
this chart calculation to arbitrary module sheaves under the degree-one cover assumption.
The chart calculation itself uses no quasi-coherence; quasi-coherence in 0B5I is needed
for the ensuing sheaf morphism and reconstruction, not this evaluation map.

Hypotheses and clauses, matched individually:

- The nonnegatively graded commutative ring is `{S : Type u} [CommRing S]`
  with `𝒜 : ℕ → AddSubgroup S` and `[GradedRing 𝒜]`. `Proj 𝒜` is the existing
  projective spectrum scheme, not a second definition. The universe `u` is arbitrary.
- The degree-one standard open cover is exactly `cover : ∀ x : Proj 𝒜,
  ∃ f ∈ 𝒜 1, x ∈ basicOpen 𝒜 f`.
- The arbitrary module sheaf is `F : (Proj 𝒜).Modules`, without any
  `IsQuasicoherent` instance or finite-type assumption.
- O(n) is `twist 𝒜 n`; F(n) is the existing scheme tensor `F ⊗ twist 𝒜 n`.
- N is written directly as `DirectSum ℤ (fun n : ℤ ↦ Γ(F ⊗ twist 𝒜 n, ⊤))`.
  The existential module structure `m` has its homogeneous action specified on every
  summand: multiplication by `s ∈ 𝒜 d` is `(F ◁ twistMul n hs).app ⊤`, landing in
  summand `n+d`. Since S and N are direct sums of homogeneous pieces, this determines
  the action completely. No arbitrary action is assumed as a hypothesis.
- For every `g ∈ 𝒜 d`, `hd : 0 < d`, the first conjunct states that
  `(unitToTwist hg).app (basicOpen 𝒜 g) 1` is an `IsFreeGenerator`.
  This is the actual canonical section g, using upstream's unnormalized `0+d` index.
- Positive homogeneous charts are indexed by `{p : S × ℕ // 0 < p.2 ∧ p.1 ∈ 𝒜 p.2}`.
  For every such f, the carrier equation for `Z f` is exactly the set of fractions
  `t/f^m` with `m : ℕ` and `t : Γ(F ⊗ twist 𝒜 (m*deg f), ⊤)`, using the actual
  `LocalizedModule.mk` quotient. Hence there are no extra or missing fraction elements.
  `Z` is an additive subgroup of that quotient, so equal representatives are literally
  the same input, and `phi : Z f →+ Γ(F, basicOpen 𝒜 f.val.1)` is well-defined and additive.
- Homogeneous-localization linearity is expressed without another module instance:
  for each `r : HomogeneousLocalization.Away 𝒜 f.val.1` and `q : Z f`, the scalar clause
  gives `q'` whose underlying localization element is `r.val • q.val`, and
  `phi f q' = awayToSection 𝒜 f.val.1 r • phi f q`. Carrier inclusion makes q' unique.
  This is precisely scalar closure and linearity for S_(f), with its canonical action.
- Evaluation `phi_f(t/f^m)=t|/f^m` is specified by the equivalent equation
  `tmulSection (phi f q) (canonical section f^m) = t|`. The canonical section is
  `unitToTwist` for `f^m`; `eqToHom` normalizes its degree `0+md` to `md`.
  Upstream `isFreeGenerator_unitToTwist`, applied to f^m, and `basicOpen_pow`
  make tensoring back bijective for m>0. At m=0 the unit section does so.
  Thus this equation uniquely determines the inverse-trivialization evaluation
  of the node; it neither asserts local surjectivity of global sections nor drops
  an equality by replacing it with an unspecified map.
- The restriction `rho f g inc` is additive and quantified over every standard-open
  inclusion. Its formula is required for every `e,c,a` satisfying `0<e`,
  `a ∈ 𝒜 c`, `g^e=a*f`, and `e*deg g=c+deg f`, and every representative `t/f^m`.
  It reads exactly `a^m • t / g^(e*m)` in the actual module localization.
  Relation witnesses exist by the recorded standard-open-inclusion theorem;
  increasing e makes the required degree nonnegative, including the zero case.
- The final clause `phi g (rho f g inc q) = F.presheaf.map ... (phi f q)`
  is the requested equality of maps on every input. Specializing q to `t/h^m`
  and the preceding restriction formula gives the explicit evaluation identity
  in the node. It holds for every relation witness, so it also gives independence
  of e,a. The input localization quotient gives fraction-representative independence.
- No finite generation, quasi-compactness, or quasi-coherence is used as a binder.

Dependency declarations read and used:

- `def-pc-proj`: Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic (`Proj`,
  `Proj.basicOpen`, `Proj.basicOpenIsoSpec`) and Scheme (`projIsoSpec`);
  the recorded upstream Proj.isAffineOpen_basicOpen_and_nonempty_iso signature/docstring
  was also read in WeilConjectures.Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic.
- `def-weil-pbc-proj-twisting-sheaf`:
  WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules (`Proj.twist`,
  `Proj.twistMul`), UnitToTwist (`Proj.unitToTwist`), and TensorObj
  (`Proj.twistPowSection`). The latter only handles degree one, so the present
  statement uses unitToTwist for arbitrary positive degree instead.
- `def-pur-sheaf-tensor-product`:
  Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses, publicly imported
  through StandardProjTwistTensor. Scheme tensor and `Scheme.Modules.tmulSection`
  are the existing sheafification tensor, as read in
  WeilConjectures.AlgebraicGeometry.Modules.TensorSection.
- `lem-sfb-standard-proj-twist-tensor`:
  Sheaf.AlgebraicGeometry.StandardProjTwistTensor (`Proj.standardProjTwistTensor`),
  with its actual multiplication, unit and associativity equations.
- `lem-weil-pbc-proj-graded-module-sheaf-exists`:
  WeilConjectures.AlgebraicGeometry.ProjGradedModuleSheafExists
  (`Proj.gradedModuleSheaf_exists`), public through StandardProjTwistTensor.
  The ordinary localized module and all representative restriction formulas
  match that declaration's chart interface. Its rho witnesses are existential,
  so this theorem existentially specifies the same canonical maps by their formulas.
- `def-weil-sheaf-of-modules-category`: Sheaf.CategoryTheory.RingedSiteModules
  (`CategoryTheory.ringedSiteModules`), the general-site abbreviation for the
  existing `SheafOfModules`; `(Proj 𝒜).Modules` is its scheme specialization.
- Proof-only: WeilConjectures.AlgebraicGeometry.ProjStandardOpenProperties
  (`Proj.standardOpenProperties`) and Mathlib.Algebra.Module.LocalizedModule.Basic
  (`LocalizedModule`, `LocalizedModule.mk`, `LocalizedModule.mk_eq`).

Edge cases checked: m=0 (unit trivialization, no division by an unintroduced
negative exponent); zero F; empty Proj and empty/nilpotent-denominator charts
(section modules and localizations are zero); arbitrary positive degrees,
unequal chart degrees and all homogeneous relation witnesses; negative twist
summands retained in N; no finite cover or algebra generators assumed.
No statement correction or dispute was needed.

Searches actually run with msearch.py:

- leanfinder: "Evaluation of fractions of twisted global sections of any module
  sheaf on Proj commutes with homogeneous standard open restrictions". Eight hits:
  structure-sheaf awayToSection/awayMap lemmas and morphism restrictions, no match
  for arbitrary module sheaves or their graded twisted global sections.
- loogle: "AlgebraicGeometry.Proj, ModuleCat". Zero hits.
- grep, AlgebraicGeometry: "GammaStar|sectionModule|fraction.*restrict|restrict.*fraction".
  Zero hits in the pinned Mathlib search index.
- leansearch: "Evaluation of homogeneous fractions of all twisted global sections
  of an arbitrary module sheaf on Proj is linear and compatible with standard open
  restrictions". Eight hits, on affine Spec module tilde or the structure sheaf of
  Proj; none states this result.
- rg in lean/WeilConjectures and lean/Sheaf for sectionModule/GammaStar,
  fraction evaluation, gradedSections and twistedSections: unrelated lisse
  sections, private twist-fraction evaluations and the downstream reconstruction
  theorem. The latter's projTwistedSections abbreviation cannot be imported here:
  its node depends on this node. The direct sum is therefore written inline,
  not redefined. Existing SerreSectionModule interfaces specialize to P1 over
  a field and do not cover this statement's arbitrary graded ring and sheaf.
- rg for both new declaration names and GammaStar in those libraries and
  dag/lean_names_upstream.json found no matching public declaration.
- The requested node-id grep in lean/WeilConjectures found no existing statement.

Validation: scompile.py compiled the final module in sandbox mode and its actual
library module name, without errors or warnings (3.5 s and 3.4 s respectively).
The transient inference problem was fixed by binding every chart index's type;
no timeout or heartbeat limit was increased in the final file.

## Second reading by Q129

Author self-audit; no independent worker was started, as required by the dispatcher
brief. The maintainer's independent delivery review remains authoritative.
I reread the node and the final module: ring and cover binders match; F is
unrestricted; all integer twists and canonical multiplication on summands are
present; phi lives on the exact fraction quotient; scalar closure and linearity,
all positive-degree charts, all degree-compatible relation witnesses and the
restriction identity are explicit. The multiplication-back equation is equivalent
to inverse trivialization because the canonical section is a free generator,
not because of quasi-coherence. The degree cast `0+md=md` and the actual canonical
section g^m were checked against UnitToTwist's full signature. The dry-run and
maintainer review should particularly check this normalization and the inline
homogeneous-localization representation. No source or node changes were made.
