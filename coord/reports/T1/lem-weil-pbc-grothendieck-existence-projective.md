## Worker report

The module `Sheaf.AlgebraicGeometry.GrothendieckExistenceProjective` states
`AlgebraicGeometry.completion_isEquivalence_of_projective_embedding`, with proof `sorry`.
It uses the existing completion functor; it introduces no definitions or extra DAG nodes.

Hypothesis and clause correspondence:

- The commutative Noetherian ring A is `(A : Type u) [CommRing A] [IsNoetherianRing A]`.
- Its ideal and adic completeness are `(I : Ideal A) [IsAdicComplete I A]`.
  This is completeness and separatedness: `AdicCompletion.of_bijective_iff` identifies
  it with the node's bijectivity of the canonical completion map.
- The scheme X is `(X : Scheme.{u})`. An arbitrary nonnegative dimension is `(n : ℕ)`.
- The closed embedding into P^n_A is
  `(i : X ⟶ ProjectiveSpace (ULift.{u} (Fin (n + 1))) (Spec (.of A)))`
  with `[IsClosedImmersion i]`. The coordinate type has n+1 elements, as required by
  the recorded projective-space definition (its index counts homogeneous coordinates).
  ULift puts those coordinates in the scheme universe without changing their number.
- The A-structure is the composite `i ≫ (ProjectiveSpace … (Spec (.of A)) ↘ Spec (.of A))`.
  Thus i is over Spec(A) by construction. Every embedding over any specified A-structure
  has precisely this composite, so this parameterization adds or loses no cases.
- The quasi-coherent ideal I O_X is
  `((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker).comap` of that composite.
  The quotient map has kernel I; its Spec morphism's kernel ideal sheaf is therefore
  the ideal sheaf associated to I. IdealSheafData.comap is scheme-theoretic pullback
  of the ideal (extension on affine charts), so this is I O_X, including nilpotents.
- The source and target categories and completion functor are exactly the existing
  `completion X J : CoherentModules X ⥤ CoherentFormalModule X J`.
  Its required `IsNoetherian X` argument is supplied explicitly by a structure term:
  `LocallyOfFiniteType.isLocallyNoetherian` on the composite supplies local Noetherianity,
  and `QuasiCompact.compactSpace_of_compactSpace` supplies compactness. Instances for
  the finite-coordinate projective projection, closed immersion, and their composite
  provide finite type and quasi-compactness. No hypothesis on X is added.
- “Is an equivalence” is `Functor.IsEquivalence` of precisely that completion functor.
- “In particular every object is isomorphic to F^wedge for coherent F” is already
  a field of this conclusion: `Functor.IsEquivalence.essSurj` gives `Functor.EssSurj`,
  whose `mem_essImage` says every formal module M is isomorphic to `(completion X J).obj F`
  for some `F : CoherentModules X`. `CoherentModules` is the full subcategory with
  predicate `RingedSpace.IsCoherent X.toRingedSpace`. No redundant conjunct is added.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` (all ideals finitely generated).
- `Mathlib.RingTheory.AdicCompletion.Basic`: `IsAdicComplete` (Hausdorff and precomplete).
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `AlgebraicGeometry.IsClosedImmersion`.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`: `AlgebraicGeometry.ProjectiveSpace`,
  its canonical base projection and finite-index properness instance. The node's older
  master-branch record is usable: the declaration is present in slopmaster2 with the same
  scheme-theoretic fibre-product definition.
- `Sheaf.AlgebraicGeometry.CoherentFormalModule`: `AlgebraicGeometry.completion`,
  `CoherentModules`, `CoherentFormalModule`. Read the actual quotient and transition-map
  construction; level `op k` means level k+1, exactly the positive levels in the node.
- `Sheaf.AlgebraicGeometry.Coherent`: `AlgebraicGeometry.RingedSpace.IsCoherent`,
  through the shared `CoherentModules` definition.

Also read Mathlib's `Scheme.Hom.ker`, `Scheme.IdealSheafData.comap`,
`Functor.IsEquivalence`, `Functor.EssSurj`, and the existing affine ideal-pullback
interface `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine`.
Dependencies are imported transitively through the three imports in the module.

Source checked: https://stacks.math.columbia.edu/tag/0885, Lemma 30.24.3 and its entire
proof. The local Stacks TeX checkout is absent on this machine, so the authoritative
Stacks page was opened. Its projective hypothesis specializes to exactly the embedding
in the node by 01W9. The declaration docstring follows all eight DAG proof steps,
including their named lemma dependencies. No statement correction or dispute was needed.

Edge cases checked before writing:

- n=0 uses one homogeneous coordinate, hence P^0 rather than an empty coordinate set.
- Empty X is allowed: no Nonempty or Nontrivial condition appears.
- A may be the zero ring; no domain, local-ring, field, characteristic or nontriviality
  condition is introduced. The corresponding empty schemes cause no typing problem.
- I=0 gives the constant coherent system and ordinary completion equivalence.
- I=top can be complete only for the zero ring because separatedness is part of
  IsAdicComplete; the statement does not accidentally assert an equivalence in a
  nonzero-ring unit-ideal case.
- Nonreduced rings and nilpotent ideals are included; using the quotient kernel rather
  than a vanishing ideal preserves the scheme structure.
- Universe u is explicit and unrestricted. No independent smaller test universe or
  finite-module-size restriction is introduced.

Searches for an existing statement (msearch.py, group T1, this item):

- leanfinder: “Grothendieck existence completion functor coherent sheaves projective
  scheme complete Noetherian ring equivalence”. Eight unrelated results, including
  ProjectiveSpectrum.StructureSheaf.structurePresheafCompForget and
  Scheme.AffineZariskiSite.sheafEquiv; no existence equivalence.
- loogle: “IsAdicComplete, Functor.IsEquivalence”. Zero hits; service reports unknown
  identifier Functor.IsEquivalence. The class was subsequently read directly in Mathlib.
- leansearch: “Grothendieck existence theorem coherent formal modules completion
  projective”. Service unavailable (Internal Server Error), recorded without a verdict.
- msearch grep: `Grothendieck.*existence|formalCompletion|CoherentFormalModule` in
  Mathlib/AlgebraicGeometry: zero hits.
- rg with the same conceptual pattern and the exact node id in
  `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and the repository's `lean/Sheaf`:
  only the shared CoherentFormalModule definitions and the different theorem
  AlgebraizeFiniteOverProper; no declaration stating the current node.

Validation: scompile.py compiled the final 65-line module on the server in 2.6 seconds,
exit code 0, without errors or warnings. All variables and universe u are explicit.
The record signature is the output of tools/stage2_delivery.py signature.

## Second reading by T1

Independently read the item node, its six statement-dependency nodes, the module,
and the actual dependency declarations. No mathematical or typing mismatch was
found, so the Lean and node record are unchanged. There are no new definition
nodes, dependency modules, or statement corrections in this delivery.

Source: the local Stacks checkout is absent. Read the authoritative pages
https://stacks.math.columbia.edu/tag/0885 and
https://stacks.math.columbia.edu/tag/01W9, then fetched the actual upstream
coherent.tex and morphisms.tex into this item's scratchpad and read
lemma-existence-projective, section-existence (including its introductory
paragraph), and lemma-H-projective. The section adds no standing hypotheses.
0885 concerns projective morphisms; the node is its H-projective specialization,
justified by 01W9, exactly as the node's source record says.

Object, hypothesis, and conclusion checklist:

1. A commutative Noetherian ring: `(A : Type u) [CommRing A]
   [IsNoetherianRing A]`. Read the recorded Mathlib Noetherian definition;
   ideals are A-submodules and finite generation is exactly the node's notion.
   Verdict: exact, with neither field nor domain hypothesis.
2. An ideal I and completeness of A: `(I : Ideal A) [IsAdicComplete I A]`.
   Read the class and `AdicCompletion.of_bijective_iff` in Basic.lean.
   Hausdorffness plus precompleteness is equivalent to bijectivity of the
   canonical completion map. Verdict: exact, including separatedness.
3. X over A: `(X : Scheme.{u})`, with structure morphism the composite of
   `i` with the canonical projective projection. Given an A-scheme and an
   embedding over A, that composite is its structure morphism; conversely
   each i defines such an A-scheme. No over-base cases are excluded.
   Verdict: equivalent parameterization, no additional assumption.
4. Some n >= 0 and a closed immersion into classical P^n_A:
   `(n : ℕ) (i : X ⟶ ProjectiveSpace (ULift.{u} (Fin (n + 1)))
   (Spec (.of A))) [IsClosedImmersion i]`. Read ProjectiveSpace's
   fibre-product body and `over` projection, and Mathlib's closed-immersion
   class. The recorded dependency indexes homogeneous coordinates, hence
   n+1 coordinates are required. The universally bound witnesses n and i
   give the assertion for every admitted embedding, equivalent to the
   node's existential hypothesis. Verdict: exact.
5. The ideal sheaf J = I O_X: the last argument of `@completion` is
   `(Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker.comap` of
   the same structure morphism. Read `Scheme.Hom.ker`, `ker_apply`,
   `IdealSheafData.comap`, and upstream `ideal_top_comap_of_isAffine`
   and `ideal_comap_appLE`. Spec(A/I) -> Spec(A) is a closed immersion,
   hence quasi-compact: its kernel sheaf corresponds to I. Comap extends
   that ideal along the ring map on affine charts. Verdict: exactly I O_X,
   with scheme structure and nilpotents retained, not radical support.
6. Coherent modules and coherent formal systems: read `CoherentModules`,
   `RingedSpace.IsCoherent`, `IsCoherentFormalModule`, and
   `CoherentFormalModule`. Coherence is finite type with finite-type
   kernels of maps from finite free modules on every open. Formal objects
   are coherent inverse systems, annihilated by the positive power at each
   level, whose transition induces the required quotient isomorphism.
   Morphisms are the compatible natural transformations. Verdict: exact.
7. The specified completion functor: `@completion X ... J`. Read its body
   through `formalCompletionFunctor`, `formalCompletionSystem`,
   `formalModuleQuotient`, and the quotient-map construction. At `op k`
   it gives F/J^(k+1)F, with canonical reductions on objects and maps.
   Named sorry theorems supply only proof obligations, never object data.
   The explicit Noetherian structure uses locally finite type and
   quasi-compactness of the closed-immersion/projective-projection
   composite; these follow from the existing properness instances.
   Verdict: no extra Noetherian-X hypothesis, no private completion copy.
8. Equivalence: `Functor.IsEquivalence` of this very functor. Read its
   full, faithful, and essentially-surjective fields. Verdict: all of
   the conclusion, neither weaker nor stronger.
9. Every formal system is isomorphic to a completed coherent module:
   the `essSurj` field and `EssSurj.mem_essImage` quantify over every target
   object and give a source object and an isomorphism. Verdict: the
   node's in-particular clause follows directly from the conclusion;
   no redundant conjunct is needed.

Edge cases: n=0 gives exactly one coordinate, hence P^0_A; an empty
coordinate type is not requested by the node. Empty X and the zero ring
are permitted without Nonempty/Nontrivial assumptions. Zero coherent
modules are included. I=0 is permitted; I=top forces A=0 by the Hausdorff
condition, avoiding a false assertion over nonzero rings. Nilpotent I,
nonreduced A, and every characteristic are included. Universe u is bound
explicitly and unrestricted; ULift raises only the coordinate index to
u, without changing its finite size. No test universe or index universe
can make a hypothesis vacuous. The module categories use the established
shared universe convention, allowing arbitrary sizes by choosing u.

Independent searches, using different words from the first worker:

- LeanFinder: `equivalence algebraization compatible coherent inverse
  systems complete base projective`. Eight affine AdicCompletion results,
  headed by `AdicCompletion.ofAlgEquiv`, no sheaf-existence statement.
- Loogle: `IsAdicComplete, ProjectiveSpace`: no hits; the service does not
  know the project declaration ProjectiveSpace, so this is not evidence
  of absence on its own.
- LeanSearch: `algebraization of compatible coherent sheaves on
  infinitesimal neighbourhoods of a projective scheme`: service unavailable
  (Internal Server Error), recorded without a mathematical verdict.
- Direct rg on pinned Mathlib/AlgebraicGeometry, upstream WeilConjectures,
  and the repository lean/Sheaf for algebraization/algebraisation,
  existence/projective, completion/equivalence, and adic/coherent.
  Results are algebraize tactics, affine completion material, the shared
  formal-category definitions, and the distinct finite-over-proper
  algebraization theorem; no declaration of this existence equivalence.

H5--H9: only the main theorem is declared, with proof `sorry`; no hollow
definitions, file-local notation, local instances, hidden lets, or unbound
variables occur. The header and both source/blueprint docstrings satisfy
the conventions. The statement docstring follows all eight node proof
steps with their dependencies. No line exceeds 100 characters. The node's
lean.statement agrees with the file signature. Changes: appended this
independent second reading only; no statement repair was necessary.
