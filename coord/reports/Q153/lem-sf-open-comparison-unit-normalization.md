## Worker report

The module Sheaf.AlgebraicGeometry.OpenComparisonUnitNormalization states precisely the
ordinary constant-coefficient comparison normalization in the node. The only postponed
proof is AlgebraicGeometry.ProEtale.openComparison_unit_normalization. Two real helper
definitions name the exact restriction comparison and the exact displayed Hom chain;
they belong to this same notion and are listed in lean.declarations. There are no new
nodes, dependency repairs or statement changes.

Hypotheses and clauses:

- Schemes U and X are `{U X : Scheme.{u}}`, the named morphism is `(j : U ⟶ X)`, and
  the open immersion is `[IsOpenImmersion j]`. No quasi-compactness or other geometric
  hypothesis is added.
- The finite discrete commutative coefficient ring is `(A : Type (u + 1)) [CommRing A]
  [Finite A]`. Discrete fixed coefficients are encoded by ModuleCat-valued sheaves,
  with no topological ring or constructibility restriction. This is the established
  common larger coefficient universe for the small sites; smaller finite rings can be
  lifted, and no relationship between scheme object and morphism universes is changed.
- The two module categories are `Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)`
  and `Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)`, and similarly over the
  other base. These are ordinary sheaves with fixed scalar actions, equivalently modules
  over the constant ring sheaf. They are not structure-sheaf modules or derived objects.
- C_T and R_T are `comparisonUpperStar` and `comparisonLowerStar` with
  `comparisonAdjunction`. The recorded `Scheme.proEtaleSiteComparisonModules` is
  definitionally this adjunction.
- e and d are the exact existing `Etale.openImmersionLowerShriek` and
  `ProEtale.openImmersionLowerShriek`. The latter is the fixed-scalar middle functor
  in the recorded `Scheme.sfIntrinsicExtensionByZero`; its defining canonical
  realization equivalences identify the two coefficient presentations. The intrinsic
  definition is imported, not copied or replaced.
- r and s are the existing `Etale.openImmersionRestriction` and
  `ProEtale.openImmersionRestriction`. eta^e and eta^d are the `.unit.app` of their
  respective `openImmersionLowerShriekAdjunction`, not the inverse-image variant of
  that adjunction.
- The specified c is exactly `openImmersionLowerShriekComparisonUpperStarIso` from
  the recorded comparison node. It is a conjugate of
  `comparisonLowerStarOpenImmersionRestrictionIso`, whose body is `Iso.refl _`.
- The specified a is `openComparisonRestrictionIso`. Its middle factor is the
  dependency's exact `supportSiteComparisonCoefficientPullbackIso`; its outside
  factors are the inverses/forwards of the canonical etale/pro-etale
  `upperStarIsoOpenImmersionRestriction`. Thus this is the same inverse-image
  comparison written in restriction coordinates, not an independent isomorphism.
- `openComparisonHomEquiv` supplies the asserted bijections as an `Equiv`. Its
  definition first applies the X comparison adjunction, then the etale open
  adjunction; `Iso.homToEquiv` postcomposes by the sectionwise right-adjoint identity;
  finally the inverses of the U comparison and pro-etale open adjunctions give the
  target Hom set. Naturality is built from the existing natural adjunction bijections
  and natural isomorphism, without additional hypotheses or existential choices.
- The theorem's first conjunct quantifies over every F, M and h and identifies the
  value of that exact Hom chain with `c.inv.app F ≫ h`. Lean composition is in
  diagrammatic order, so this is exactly h composed with c_F inverse.
- Its second conjunct quantifies over every F and reads
  `C_U.map eta^e ≫ a.hom.app (e.obj F) ≫ s.map (c.hom.app F) = eta^d` at C_U F.
  This is exactly the stated unit normalization, with the same a and c as above.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.OpenImmersion: AlgebraicGeometry.IsOpenImmersion.
- Sheaf.CategoryTheory.RingedSiteModules: CategoryTheory.ringedSiteModules,
  the transparent general-site SheafOfModules encoding.
- Sheaf.AlgebraicGeometry.ProEtaleSiteComparison:
  AlgebraicGeometry.Scheme.proEtaleSiteComparison and proEtaleSiteComparisonModules.
- WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs:
  AlgebraicGeometry.Etale.openImmersionLowerShriek, openImmersionRestriction,
  upperStarIsoOpenImmersionRestriction and openImmersionLowerShriekAdjunction.
- Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero:
  AlgebraicGeometry.Scheme.sfIntrinsicModuleEquivalence and sfIntrinsicExtensionByZero.
- Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence:
  AlgebraicGeometry.ProEtale.supportSiteComparisonCoefficientPullbackIso, including
  its explicit conjugation of the sectionwise direct-image square.
- Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison:
  AlgebraicGeometry.ProEtale.openImmersionLowerShriekComparison_coherence and the
  reexported canonical openImmersionLowerShriekComparisonUpperStarIso.
- The existing upstream fixed-scalar comparison adjunctions and open adjunctions
  supply all Hom equivalences; Mathlib Iso.homToEquiv supplies postcomposition.

Proof dependencies are imported directly or through their recorded statement modules.
The pro-etale intrinsic adjunction, realization transport and open-unit evaluation
modules are proof-only imports. The theorem docstring gives all seven DAG proof steps,
including the projection-unit computation and the compatibility with the fixed a.

Edge cases: j = identity is allowed and uses the actual canonical comparisons; U empty
and X empty are allowed, without any point or nonempty binder; F = zero and M = zero
remain in the unrestricted Hom quantifiers; the zero ring is allowed by CommRing and
Finite, with no Nontrivial assumption. No geometric-stalk conservativity is used.

Searches made (2026-10-17):

- msearch.py leanfinder, query "open immersion etale proetale comparison extension by
  zero adjunction unit normalization": 8 hits, including Scheme.Modules restriction
  unit/counit lemmas, all for structure-sheaf modules rather than these sites.
- msearch.py leansearch, query "comparison extension by zero etale proetale unit":
  8 unrelated hits (etale morphisms, square-zero extensions, etc.); no exact theorem.
- msearch.py loogle, query "Adjunction.conjugateIsoEquiv, Adjunction.homEquiv":
  unknown identifier Adjunction.conjugateIsoEquiv; subsequent source inspection finds
  CategoryTheory.conjugateIsoEquiv and unit_conjugateEquiv_symm, the generic tool only.
- msearch.py grep, query "conjugate.*unit|openImmersionLowerShriekComparison" in
  CategoryTheory: 9 generic conjugation/counit hits, no site-specific normalization.
- rg over WeilConjectures/SixFunctors/ProEtale finds the canonical c and the sectionwise
  right-adjoint identity in Derived/LowerShriekComparison.lean. The current finite
  coefficient version was read with scompile.py --source. Neither states both formulas.
- rg over lean/Sheaf for openImmersionLowerShriekComparison and comparison/unit
  patterns finds the recorded comparison coherence and unrelated unit laws; none has
  this exact Hom chain plus this canonical mixed unit equation.
- rg for the item's id in the upstream WeilConjectures tree gives no match.
- rg of dag/lean_names_upstream.json and Mathlib sources confirms the generic conjugation
  node; the proposed full declaration names are new (also confirmed by compilation).

The source was read locally in literature/stacks-project/proetale.tex, lines 5076--5087:
Tag 09AF proves the comparison by the common right adjoint. The DAG's agent refinement
records the two natural normalization consequences of this construction. No node fault
or disputed statement was found. The module compiled cleanly using the required
scompile.py wrapper, including both sandbox and library-mode checks.

## Second reading by Q153

I reopened the node and the complete Lean file for a separate clause-by-clause pass.
The dispatcher prohibits starting another agent; this is a self-check, with the
maintainer's independent delivery review still required. I checked the two composition
orientations explicitly: the Hom formula starts with c inverse and then h, while the
unit formula starts with C_U of the etale unit, then the canonical a, then s of c.
The source and target of every arrow coincide with the node's display. The Hom helper
uses the forward sectionwise theta (not its inverse), followed by the two inverse
adjunction equivalences, which has the asserted orientation. The restriction comparison
uses the inverse etale localization isomorphism first and the forward pro-etale one
last. The finite coefficient category, both open units, all universally quantified
sheaves, and the identity/empty/zero cases are retained. The only change from this
reading was to add explicit main-definition and main-statement documentation. No
mathematical mismatch was found.
