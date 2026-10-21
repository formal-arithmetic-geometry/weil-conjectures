## Worker report

The module `Sheaf.CategoryTheory.RingedSiteFiniteRetractDualExact` states the complete
finite-free-retract calculation, with a single postponed theorem
`SheafOfModules.ringedSite_finite_retract_dual_exact`. Its three helper definitions contain
real data: the standard coordinate projection, the section `p(u_j)`, and the slice-linear
map `u_j^* i`. No alternative sheaf, internal Hom, or localization is constructed.

Hypotheses and clauses, matched to the node:

- The small ringed site is `{C : Type c} [Category.{v} C] {J : GrothendieckTopology C}`.
  Both site universes remain independent. The universe bound is `max c v w`, used for
  coefficients and modules; this implements `def-weil-size-convention`. `R` is a sheaf
  of commutative rings. The sheafification and locally-bijective instances are the
  general-site interface to the abelian module category, available for small sites
  relative to this bound. They impose no geometric or coefficient restrictions.
- `T : ringedSiteModules ...` uses the dependency's recorded module category. Its ring
  sheaf is obtained by the existing `sheafCompose` forgetful functor.
- The nonnegative finite rank is `n : ℕ`. The basis index is `ULift.{max c v w} (Fin n)`:
  this is the same n-element set in the universe required by Mathlib's `free` constructor.
  The binders `i`, `p`, and `hip : i ≫ p = 𝟙 T` are exactly the supplied splitting.
- The dual is the recorded `homObj T (unit ...)`. The first conjunct says that
  precomposition with p and then i is the identity for every target F. For F = R this
  is precisely the displayed dual splitting. These are the components of the existing
  natural transformations `(homFunctor R).map p.op` and `(homFunctor R).map i.op`;
  the componentwise formulation avoids elaborating a large equality of functors.
- The existential family `e F` identifies `homObj (free ...) F` with the existing finite
  coproduct of copies of F. The coordinate equation specifies evaluation at `u_j`, so
  these are the canonical coordinate isomorphisms, not arbitrary choices. The next
  equation specifies naturality under every `f : F ⟶ G` via `Limits.Sigma.map`.
  Specializing `e` to `unit ...`, its target is definitionally the same `free ...`.
  The following composite identity explicitly displays the finite-free retract of the
  dual after this coordinate-dual identification.
- `finiteRetractVector p j U` is `(ιFree j ≫ p)(1)` on U. The standard projection is
  `Sigma.desc (fun k ↦ if k = j then 𝟙 _ else 0)`. Restricting `i` followed by this
  projection gives `finiteRetractCovector i j U`, a section of the recorded internal
  Hom, which is literally a linear map on the slice.
- The next two universally quantified conjuncts are exactly
  `∑ j, λ_j(t) • t_j = t` and `φ = ∑ j, φ(t_j) • λ_j`. Equality of internal-Hom
  sections means equality of maps on the whole slice, not only evaluation at its
  terminal object. The `@id (R.obj.obj U)` terms specify the scalar type without
  changing the section or adding an assumption.
- The existential isomorphism `d` specifies both directions: its forward component,
  evaluated at every object W of every slice, sends t to the functional evaluating
  φ at the restriction of t to W; its inverse has exactly the stated finite sum
  `∑ j, α(λ_j) • t_j`. The full forward evaluation formula uniquely characterizes
  the canonical bidual map; no arbitrary isomorphism replaces it.
- The `∀ S : ShortComplex ..., S.ShortExact → ... .ShortExact` conjunct gives exact
  internal Hom on every short exact sequence. `hzero` merely packages the composable
  pair as Mathlib's `ShortComplex`, and is part of the conclusion. In particular, no
  surjectivity on sections is substituted for epimorphy of sheaves.
- Restriction is expressed both intrinsically and explicitly. All `e F` and `d` are
  isomorphisms of sheaves, so their two maps commute with every restriction; the
  precomposition maps are the existing `homObjMap` sheaf maps. The formulas quantify
  over every U, and the forward bidual formula over every W in the slice. The final
  conjunct explicitly gives restriction of `t_j` and `λ_j`. Together with the slice
  definition of `homObj` and the uniquely characterized coordinate isomorphisms, these
  statements give the displayed identities on every localized site and compatibility
  with successive localization. The inverse formula therefore restricts term by term.

Dependencies read and used:

- `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules` is the
  transparent abbreviation of the existing Mathlib `SheafOfModules` category.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`,
  `SheafOfModules.homObj`, `homObjMap`, `homFunctor`. The full definitions and signatures
  were read, including their use of `PresheafOfModules.restrictOver` and their maximum
  universe for slice morphisms. The corresponding presheaf source was also read.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`,
  `SheafOfModules.overFunctor`, `over`, `Hom.over`, `overMap`, `overFunctorMap`;
  these are the recorded localization interface, on `GrothendieckTopology.over` and
  `Sheaf.over`. Their sectionwise descriptions match the slice formulas used here.
- `def-weil-size-convention` is recorded as a metatheoretic convention, with no Lean
  declaration; it is rendered by explicit universes, not by a duplicate definition.
- Mathlib `free`, `ιFree`, `unit`, `Limits.Sigma.desc`, `Limits.Sigma.map`, and
  `ShortComplex.ShortExact` supply all remaining constructions.

Source read: `literature/stacks-project/sites-cohomology.tex`,
`lemma-dual-perfect-complex` (Tag 08JJ), especially the final two paragraphs;
`sites-modules.tex`, `lemma-internal-hom`, `lemma-internal-hom-restriction`,
and `lemma-abelian`. The theorem docstring follows all nine steps of the DAG proof.

Edge cases checked before writing: n=0 has empty sums and forces T to be zero through
its retract of the zero free object; the zero ring needs no nontriviality assumption;
no object or covering is assumed inhabited; empty-cover objects cause no exceptional
case. A site with unequal object and morphism universes is retained. Arbitrary T,
all coefficient sheaves F, all sections of internal Hom, and all short exact sequences
are quantified. There is no statement correction or disputed clause.

Searches for an existing statement:

- msearch `leanfinder`: "Internal dual of a retract of a finite free sheaf on a ringed
  site is reflexive and internal Hom is exact". Hits included ordinary module
  reflexivity, `SheafOfModules.free` interfaces, and
  `CategoryTheory.InternallyProjective.ofRetract`; none states this sheaf calculation
  with the dual-basis inverse and localization formulas.
- msearch `loogle`: `SheafOfModules.hom, Module.Dual`; returned no hits, with
  `SheafOfModules.hom` unknown. The actual project name is `homObj`, read directly.
- msearch `grep`: `dual.*retract|retract.*dual`; returned categorical retract and
  split-monomorphism infrastructure, no internal sheaf-dual theorem.
- msearch `leansearch`: "Internal sheaf Hom from a direct summand of a finite free
  sheaf preserves short exact sequences and the sheaf is reflexive". Eight hits,
  including `CategoryTheory.sheafHom`, `SheafOfModules.free`, `ιFree`, and
  `freeHomEquiv`; none is the requested theorem.
- Direct rg over both `lean/WeilConjectures` and `lean/Sheaf` for the node id,
  finite/retract and dual/retract patterns, and the proposed names. The exact item
  and names were absent. Read the related upstream `FiniteFreeInternalHomExact`,
  `InternalHomFree`, `InternalHomOver`, `Bidual`, and
  `FiniteProjectiveInternalHomEvaluation`: these provide parts of the calculation,
  with the convenience duality interfaces specialized to equal site universes, and
  do not state the current node. The existing project finite-projective lift and
  flat finite-presentation retract nodes concern existence of local splittings,
  rather than this internal-dual calculation. Mathlib and the upstream name index
  had no collision with the proposed declarations.

Validation: every delivered Lean file is compiled through the prescribed `scompile.py`;
only its expected sorry warning is accepted. Early iterations diagnosed the finite-index
universe mismatch and expensive elaboration; the final result and delivery preflight are
recorded by the wrapper output.

## Second reading by Q118

This is a self-audit, not an independent agent review: the dispatcher brief forbids
starting other agents and assigns independent review to the maintainer. Re-read the
node against the module clause by clause. The basis index must be universe-lifted;
using `Fin n` directly does not meet Mathlib's free-sheaf signature. The natural splitting
is encoded through the components of the existing natural transformations. The
coordinate family has an explicit evaluation characterization and naturality equation;
the dual retract specializes that same family, so it cannot use a different
identification. The bidual specifies evaluation at every object of every slice and
specifies its inverse, so it cannot be replaced by abstract reflexivity. Exactness is
categorical short exactness. Restriction uses sheaf maps and the explicit section and
slice formulas. The rank-zero and zero-ring cases remain included. No dependency repair,
new definition node, or change of the mathematical statement is needed.
