## Worker report

The module `Sheaf.AlgebraicGeometry.UnboundedCompactSupportProperComposition` states
`lem-sf-unbounded-compact-support-proper-composition`. It changes only this node's `lean`
record. It introduces no other DAG statement and makes no statement correction.
There are two canonical assembly definitions and three theorems, each with proof `sorry`.
Every declaration has the node's source and blueprint tag; the full six-step DAG proof
is retained in the principal theorem's docstring.

Hypotheses, individually:

- The field is `(k : Type u) [Field k]`.
- The coefficient ring is `(A : Type (u + 1)) [CommRing A] [Finite A]`. It is not required
  to be a field, nontrivial, or of invertible characteristic.
- The schemes are `X Y S : Scheme.{u}`, each with its given `.Over (Spec (.of k))`.
  Their separatedness is `IsSeparated` of their respective structure morphisms; their
  finite type is the pair `LocallyOfFiniteType` and `QuasiCompact` of those morphisms.
- The morphisms are `(f : X ⟶ Y) (g : Y ⟶ S)`, with `IsOver` of the common base for
  morphisms of k-schemes. Properness is `[IsProper f]`. The separated finite-type
  hypotheses on g are `[IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]`.
  Those properties for f and the composite are supplied by the existing instances.
- The refinement clauses use the same hypotheses for a single `(h : X ⟶ Y)` and apply
  separately to f, g and `f ≫ g`. This avoids copying a universally quantified clause
  three times. Their separated finite-type hypotheses are stated explicitly.
- The compactification choices are arbitrary `Compactification f`, `Compactification g`
  and `Compactification (f ≫ g)`. No choice is required to be dense, to have a Cartesian
  refinement square, or to agree with a globally chosen compactification.

Clauses, individually:

1. The candidates are the recorded
   `rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c`, definitionally
   `D(c.i_!) ⋙ R(c.g_*)`, on the existing unbounded derived category of ordinary
   small-etale module sheaves. No pro-etale category or bounded subcategory is used.
2. A proper refinement is exactly `r : c.Refinement d`: `r.hom` is the proper ambient map,
   `r.i_hom` fixes the source open and `r.hom_g` fixes the target. The instance
   `Compactification.Refinement.isProper` supplies its properness.
3. `unboundedEtaleProperRefinement_normalization` provides the sheaf isomorphism θ and
   natural derived isomorphism γ for **each** such r. Its first conjunct fixes θ by equality
   of the composites into the common direct image `(d.i)_*`; the inclusion of extension
   by zero into direct image is the existing `openImmersionLowerShriekToLowerStar`.
   Thus θ is precisely the proper-support identification that restricts to the identity
   on the source, rather than an arbitrary sheaf isomorphism.
4. Its second conjunct quantifies over every K-injective J, every K-injective I and every
   quasi-isomorphism `ρ : c.i_! J ⟶ I`. The left side evaluates γ at `Q J`, transports
   `D(c.i_!)(Q J)` along `mapDerivedCategoryFactors`, applies `R(r.hom_*)` to ρ and uses
   `rightDerivedFunctorObjQIso I`. The right side is exactly the localization of
   `d.i_! J --θ--> r.hom_* c.i_! J --r.hom_*ρ--> r.hom_* I`.
   These `[I.IsKInjective]` and `[QuasiIso ρ]` hypotheses are precisely the two clauses
   of the recorded `CochainComplex.IsKInjectiveResolution` abbreviation.
5. Its last conjunct identifies the **existing** common-refinement isomorphism from d to c
   with γ whiskered by `R(d.g_*)`, followed by the canonical derived direct-image
   compositor using `r.hom_g`. All factors are natural transformations, and the left
   side is a natural isomorphism. This proves invertibility for arbitrary refinements
   without defining a second comparison map.
6. `unboundedEtaleProperRefinement_coherence` gives the identity and cocycle equations for
   `rightDerivedLowerShriekOfCompactificationIso`. With the preceding normalization,
   `C_r = I(d,c)`, so the identity equation is the identity-refinement law and the
   cocycle with reversed compactification indices is the composite-refinement law.
   Its last conjunct states explicitly that for any common refinement e and any arrows
   `r : e.Refinement c`, `s : e.Refinement d`, the comparison is
   `I(c,e).hom ≫ I(d,e).inv = I(c,d).hom`. Thus it is independent of both the common
   refinement and its chosen arrows; the second conjunct is the requested cocycle.
7. `unboundedEtaleProperCandidateIso A f c` compares c with
   `Compactification.ofIsProper f` and then applies the canonical derived identity-open
   isomorphism, followed by the functor left unitor. Its data are written in full,
   using `Adjunction.leftAdjointIdIso`, `upperStarId`, and termwise derived descent.
   The first two conjuncts of `unboundedEtaleProperComposition_normalization` state its
   compatibility with every compactification comparison and its normalization at the
   trivial compactification (identity after the canonical identity-open identification).
8. `unboundedEtaleProperCompositionIso A f g d c` is the required α:
   `R(f_*) ⋙ Rg_!^d ≅ R(f ≫ g)_!^c`. It uses the explicit closure tower `c.ofComp d`,
   the inverse of the proper identification on its restricted compactification of f,
   the existing `rightDerivedLowerShriekOfCompactificationCompIso`, and the existing
   comparison of its output with c. This is an explicit assembly of canonical maps,
   with no `Nonempty` choice, arbitrary arrow, or additional invertibility hypothesis.
9. The principal theorem's third conjunct says α is computed by **every** tower d,e,
   using its properly normalized f candidate, the proper/open model composition map,
   and the output common-refinement comparison. The existing model map is explicitly
   constructed from `openImmersionLowerShriekLowerStarExchange`, open composition,
   and proper derived direct-image composition. The final conjunct is the commuting
   square for arbitrary pairs of compactifications of g and gf. By clause 5 these
   include all proper-refinement comparisons. Together with the first conjunct for f,
   these give compatibility with all three compactification choices in the node.
10. Naturality in the input is built into every `≅` between functors. The domains are
    full unbounded `DerivedCategory` categories: no input has boundedness,
    constructibility, finite Tor amplitude, or any other restriction.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`,
  `IsSeparated` and `UniversallyClosed` (including their defining signatures).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`:
  `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`.
- `Sheaf.AlgebraicGeometry.CompactifiableOverField`:
  `AlgebraicGeometry.hasCompactification_of_finiteType_over_field`; its defining
  compactification data are the existing `AlgebraicGeometry.Compactification` in
  `WeilConjectures.Compactification.Defs`. Compactification existence adds no input
  assumption: the node already supplies arbitrary choices, and the field theorem
  ensures they exist in precisely the stated setting.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification`.
- `Sheaf.AlgebraicGeometry.DerivedCategories` and upstream `.Derived.Coefficients`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule` (the unabbreviated same category is
  used in the signatures), and Mathlib's `DerivedCategory.Q`.
- `Sheaf.AlgebraicGeometry.KInjectiveResolutions`:
  `CochainComplex.IsKInjectiveResolution`, expanded through its recorded
  `CochainComplex.IsKInjective` and `QuasiIso` clauses in the representative formula.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded`:
  `rightDerivedLowerShriekOfCompactificationIso`, constructed through the existing
  common refinement. The more primitive comparison there requires a Cartesian square
  and does not cover this node's arbitrary-refinement normalization.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition`:
  `rightDerivedLowerShriekOfCompactificationCompIso`, whose real definition is the
  proper/open tower assembly. `.UpperLowerStar` provides the canonical direct-image
  compositors. The existing `nonempty_iso_rightDerivedLowerShriek_comp` lacks this
  node's normalizations and coherence, and is not substituted for them.

All recorded, already stated proof dependencies are imported: Noetherian and geometric
permanence through Mathlib, `Sheaf.Paper.UnboundedProperOpenInterchange`,
`Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`,
`WeilConjectures.Compactification.CategoryBaseChange`,
`Sheaf.AlgebraicGeometry.CompactifiableCompatibleTower`, and
`Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence`. Statement dependencies
are public imports; imports used only by the postponed proofs are not public.

Edge cases checked before writing: the empty scheme and empty open, zero complexes and
zero coefficient ring, identity refinements, composite refinements, different or parallel
common-refinement arrows, noncartesian refinements with extra boundary components, the
trivial compactification of a proper f, identity f, and a finite ring whose characteristic
is not invertible on the schemes. None is excluded. The site/coefficient universes follow
the recorded ordinary-etale API: schemes at u, coefficients and module carriers at u+1;
every universe and binder is explicit and `autoImplicit` is disabled. No additional
Noetherian or dimension hypothesis is imposed.

Searches made:

- `msearch.py leanfinder`, query "Unbounded ordinary etale compact support composition
  with proper derived direct image": eight hits on proper morphism composition and
  underived scheme-module pushforward; none states the node.
- `msearch.py loogle`, query `"rightDerived", "comp"`: twelve generic right-derived
  functor/localizer comparisons; none fixes this geometric proper/open map or its
  compactification coherence.
- `msearch.py grep`, query `lowerShriek|compactSupport|extensionByZero` in
  `CategoryTheory`: no hits.
- `rg` in upstream `WeilConjectures` and `lean/Sheaf` for refinement, proper/open,
  `rightDerivedLowerShriek` and composition: read the full unbounded independence,
  composition, and proper/open exchange source modules. Existing constructions were
  reused. `UnboundedEtaleCompactSupportComparisons` already assembles a general
  composition isomorphism; its refinement normalization uses a separate graph
  normalization datum and does not state this node's K-injective equation for every
  proper refinement. No duplicate of its composition construction was written:
  the definitions here specialize the existing tower map directly to a proper input
  and the trivial-compactification normalization required here.
- Upstream grep for the exact item id gave no declaration. Searches for all five new
  full declaration names in Mathlib, upstream and existing `lean/Sheaf` gave no hits.
  `dag/lean_names_upstream.json` was also consulted for the comparison/composition names.

Source read: `literature/stacks-project/more-etale.tex`, the torsion-ring paragraph of
section 0F7H, the full common-refinement construction of 0F7I, the tower construction
and choice-independence argument of 0F7J, and the K-injective construction in 0F7B (b).
No `STATEMENT-DISPUTED` flag or node fault was found.

Validation: `scompile.py N8 lem-sf-unbounded-compact-support-proper-composition` compiled
this file cleanly in both the sandbox and library-module checks (about 8 seconds each).
The only postponed proofs are the three named theorems above. The two definitions have
real data. The delivery dry run is the final check; no push is requested by this worker.

## Second reading by N8

I independently read the node, the delivered module, all six statement-dependency
records and their actual declarations, and the cited Stacks source before assessing
the worker's report. No statement correction, new node, or dependency repair is
needed. The Lean module and node record are retained unchanged; this section is the
second reader's addition.

Objects and hypotheses, followed by every conclusion clause:

1. **Field and coefficients.** The node introduces a field k and a finite commutative
   ring A. Every theorem binds `(k : Type u) [Field k]` and
   `(A : Type (u + 1)) [CommRing A] [Finite A]`. These are the requested objects;
   neither nontriviality of A nor invertibility of its characteristic is assumed.
   Verdict: exact.
2. **Schemes over the same field.** The principal theorem binds
   `{X Y S : Scheme.{u}}` with three `.Over (Spec (.of k))` instances. For each
   structural morphism, `IsSeparated`, `LocallyOfFiniteType` and `QuasiCompact`
   render separatedness and finite type. The two generic refinement theorems use
   the same source and target hypotheses. Verdict: exact; finite type is the
   recorded conjunction, not finite presentation or smoothness.
3. **Morphisms.** `(f : X ⟶ Y) (g : Y ⟶ S)` and their `IsOver` instances make
   morphisms of the given k-schemes; `[IsProper f]` renders properness.
   `[IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]` renders precisely
   the hypothesis on g. Mathlib's `IsProper` includes universal closedness and
   local finite type, and universal closedness supplies quasi-compactness.
   No extra geometric hypothesis is present. Verdict: exact.
4. **Compactification choices and candidates.** `Compactification f`,
   `Compactification g`, and `Compactification (f ≫ g)` use the recorded
   structure: ambient scheme Z, open immersion i, proper g, and factorization.
   There is no density requirement. The reused
   `rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c`
   is definitionally `D(c.i_!) ⋙ R(c.g_*)`. Its domain is exactly
   `DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))`.
   I checked `DerivedCategoryModule` in the recorded coefficient source; this
   unabbreviated category is the same ordinary unbounded category. Verdict: exact.
5. **Refinement.** In `unboundedEtaleProperRefinement_normalization`,
   `{c d : Compactification h} (r : c.Refinement d)` gives the ambient map,
   `r.i_hom : c.i ≫ r.hom = d.i`, and `r.hom_g : r.hom ≫ d.g = c.g`.
   I read `Refinement.isProper`: properness follows from the proper ambient
   structural maps. Thus no required properness is lost by its not being an
   explicit structure field. No cartesian hypothesis is added. Verdict: exact.
6. **The sheaf proper/open identification.** The existential θ has source
   `d.i_!` and target `c.i_! ⋙ r.hom_*`. Its first conjunct identifies its
   composite into `d.i_*` with `openImmersionLowerShriekToLowerStar` for d.
   This is the identification of proper-support subsheaves in Stacks 0F7B,
   and forces the identity on the source open. It is stronger than merely
   saying some isomorphism exists only in the sense of specifying the very
   canonical identification the node requests. Verdict: exact normalization.
7. **K-injective representative formula.** The next conjunct quantifies over
   each K-injective J on X, each K-injective I on c.Z, and each quasi-isomorphism
   `ρ : c.i_! J ⟶ I`. I checked the recorded `IsKInjectiveResolution`:
   it is precisely `QuasiIso ρ ∧ I.IsKInjective`. The left side evaluates γ
   on `DerivedCategory.Q.obj J`, uses `mapDerivedCategoryFactors`, maps ρ
   by `R(r.hom_*)`, and then uses `rightDerivedFunctorObjQIso I`.
   The right side is Q applied to θ followed by `r.hom_*ρ`.
   Thus the displayed equation is exactly the specified representative map,
   with the necessary localization identifications. Verdict: exact, including
   universal rather than chosen-resolution quantification.
8. **Proper-refinement comparison and invertibility.** The final conjunct
   identifies `(rightDerivedLowerShriekOfCompactificationIso A d c).hom`
   with γ whiskered by `R(d.g_*)`, the associator, and the derived direct-image
   compositor using `r.hom_g.symm`. This has direction F_d to F_c, as the
   node requires. Both γ and the common-refinement comparison are natural
   isomorphisms. I read the upstream definition: its primitive comparison
   requires a cartesian square, whereas this equality handles every proper
   refinement through the existing common-refinement isomorphism. Verdict: exact.
9. **Identity, composition, and common refinements.**
   `unboundedEtaleProperRefinement_coherence` states `I(c,c) = Iso.refl`,
   `I(c,d) ≪≫ I(d,e) = I(c,e)`, and, for every common refinement e and
   arrows `r : e.Refinement c`, `s : e.Refinement d`,
   `I(c,e).hom ≫ I(d,e).inv = I(c,d).hom`.
   In combination with item 8, C_r is I(d,c), so these equations give the
   identity/composition laws for actual refinement maps and independence of
   the common object and both arrows. The arrow binders are intentionally
   absent from the expression after normalization: that absence expresses
   arrow independence. The generic h can be specialized to each of f, g,
   and `f ≫ g`; its geometry follows from the principal hypotheses.
   Verdict: all coherence clauses present.
10. **Proper normalization.** `unboundedEtaleProperCandidateIso A f c`
    first compares c with `Compactification.ofIsProper f`, then uses
    `Adjunction.leftAdjointIdIso`, `upperStarId`, termwise derived descent,
    and the left unitor. These are real canonical data. The principal
    theorem's first conjunct makes this identification compatible with
    every comparison of compactifications of f; its second gives exactly
    the identity-open normalization at `(id_X,f)`. Verdict: exact.
11. **Composition isomorphism and its specified construction.**
    `unboundedEtaleProperCompositionIso A f g d c` has source
    `R(f_*) ⋙ Rg_!^d` and target `R(f ≫ g)_!^c`, hence the mathematical
    order `Rg_! Rf_*`. Its body uses the concrete closure tower `c.ofComp d`,
    the inverse of the proper identification of its restricted f model,
    `rightDerivedLowerShriekOfCompactificationCompIso`, and output comparison.
    I read that upstream model definition: it uses proper/open exchange,
    derived direct-image composition, and degreewise open composition.
    The principal theorem's third conjunct gives this formula for every
    tower e, not just the tower used in the definition. Verdict: exactly
    the canonical composition required, not a bare existence assertion.
12. **Naturality and compatibility of all choices.** Each displayed `≅`
    is a natural isomorphism of functors. The final conjunct commutes the
    composition map with arbitrary comparisons d₁ to d₂ for g and c₁ to c₂
    for gf. Together with item 10 for f and item 8 identifying every proper
    refinement, this is compatibility with all three compactification choices.
    The entire unbounded domain is used, with no boundedness,
    constructibility, or Tor-amplitude restriction. Verdict: exact.

Source-wide assumptions were checked in `more-etale.tex`: section 0F7H assumes
separated finite type and a quasi-compact quasi-separated target; 0F7I and 0F7J
use quasi-compact quasi-separated schemes. The finite-type separated k-schemes
here satisfy these assumptions. The torsion-ring paragraph explicitly uses the
whole unbounded category. Tag 0F7B(b) applies because finite rings are torsion.
Its construction identifies proper-support subsheaves inside the common direct
image, precisely the θ normalization above. The proof of 0F7J uses the same
proper/open tower and refinement-pasting argument. No omitted ambient hypothesis
or departure from the source was found.

Edge cases: empty source or target schemes, empty open immersions, zero complexes,
the zero coefficient ring, identity f and g, trivial proper compactifications,
identity and composite refinements, parallel refinement arrows, and added boundary
components mapping into the source open are all admitted. In particular there is
no density or pullback-square restriction on a refinement. There is no degree n
parameter or index-set nonemptiness condition; all integer cochain degrees occur.
The characteristic of k is arbitrary, including zero and primes dividing the
order of A. `universe u` is explicitly bound, the scheme/field universe is u,
and coefficients and module carriers are u+1, exactly the dependency encoding.
No new universe equality is assumed and `autoImplicit` is disabled.

Independent searches (2026-10-16): `msearch.py leanfinder` with
"canonical isomorphism extension by zero proper pushforward unbounded derived
compactification refinement" returned eight unrelated complex-extension and
bounded-representative declarations. `msearch.py loogle` with
`"rightDerivedLowerShriek"` returned no hits. `msearch.py grep` with
`refinement|compactification` returned general Mathlib cover and Noetherian results,
not the specified statement. Direct `rg` searches in Mathlib, upstream
`WeilConjectures`, and `lean/Sheaf` used `proper`, `CandidateIso`, `CompIso`,
`refinement`, and normalization/coherence combinations. I opened upstream
`LowerShriek`, `LowerShriekIndependenceUnbounded`, `LowerShriekComposition`,
and `Composition`, plus the project's `UnboundedEtaleCompactSupportComparisons`.
The upstream proper-coincidence theorem returns only `Nonempty`, and the
composition theorem also returns only an unspecified existence result. The
project's existing graph-normalization interface does not give this node's
K-injective representative formula for every proper refinement. Its global
composition assembly is already reused here through the same primitive tower
map; no existing exact declaration replaces the delivery. The five full new
names are absent from Mathlib, upstream, `lean/Sheaf`, and the upstream name
index. No second definition of a dependency notion was found.

There are no new definition nodes or dependency modules to audit. The two helper
definitions contain real composites, not `sorry`, arbitrary isomorphisms, or
choices from undetermined existence. The three named theorem bodies are solely
`sorry`; their docstrings identify the source and blueprint node, and give the
corresponding proof steps. The principal docstring retains the full six-step
node proof. All declarations are listed in `lean.declarations`, and the recorded
`lean.statement` is verbatim the principal signature before `:= by`.
All lines are at most 100 characters and all variables/universes are bound.

Mismatches and repairs: none. Only this independent second-reading section was
added. `scompile.py N8 lem-sf-unbounded-compact-support-proper-composition` compiled
the delivered file cleanly in both sandbox and library-module mode (6.5 s and
8.0 s), with no warnings or errors. Delivery preflight and push follow below.
