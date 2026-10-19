## Worker report

The module `Sheaf.AlgebraicGeometry.ChowProjectiveClosedImmersions` states
`AlgebraicGeometry.chow_projective_closed_immersions`, with its whole proof `sorry`.
No definitions, helper theorems, dependency repairs or statement changes are needed.
The source is the current blueprint's `sk-thm-chow-projective` node
`det-chow-projective-closed-immersions.md` and the two parts of its proof file.
The declaration docstring carries all six DAG proof steps, including the empty-coordinate case.

Hypotheses and objects, clause by clause:

- The schemes `S`, `X`, and the given Chow modification `X'` are arbitrary `Scheme.{u}`.
- The finite homogeneous coordinate set is `(N : Type u) [Finite N]`, matching the
  coordinate-set interface of `exists_chow_projective_qcqs`. There is no nonemptiness premise.
- The qcqs base is `[CompactSpace S] [QuasiSeparatedSpace S]`.
- The proper morphism is `(f : X ⟶ S) [IsProper f]`.
- The given proper surjection is `(π : X' ⟶ X) [IsProper π] [Surjective π]`.
- The given immersion is `(i : X' ⟶ ProjectiveSpace N S) [IsImmersion i]`.
- Compatibility over the base is `h : i ≫ ProjectiveSpace N S ↘ S = π ≫ f`.
  Thus the binders quantify over precisely data of the dependency's existential conclusion,
  rather than choosing one existential witness or asserting new existence.

Conclusions, in order:

- Properness of the composite is `IsProper (π ≫ f)`.
- Closedness of the immersion over `S` is `IsClosedImmersion i`.
- Projectivity of the composite is `IsProjective (π ≫ f)`.
- The canonical pair `(π,i)` under the identification with projective space over `X` is
  `ProjectiveSpace.liftBaseChange π i h.symm`. Its closedness is the fourth conjunct.
- The specified composite with the projection is the fifth conjunct,
  `ProjectiveSpace.liftBaseChange π i h.symm ≫ ProjectiveSpace N X ↘ X = π`.
- Projectivity of `π` is `IsProjective π`, the last conjunct.

This uses the actual canonical construction, not an arbitrary map or an additional
commutativity premise. Reading `ProjectiveSpace.liftBaseChange` shows it is the lift into
`ProjectiveSpace N X` for the Cartesian square `ProjectiveSpace.isPullback_map N f`,
with components `i` and `π`. This is exactly the displayed fibre-product pair in the node.
The use of `h.symm` only orients the input equality in that construction's convention.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.ChowProjectiveQcqs`,
  `AlgebraicGeometry.exists_chow_projective_qcqs`: fixes the finite-set Chow data interface.
  Its module is publicly imported, along with the modules of the remaining statement dependencies.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `AlgebraicGeometry.IsProper`;
  also its separatedness and universal-closedness parents, read in their source modules.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`; and the imported
  `Mathlib.AlgebraicGeometry.Morphisms.Immersion`, `AlgebraicGeometry.IsImmersion`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`,
  `AlgebraicGeometry.IsHProjective` and `AlgebraicGeometry.IsProjective`:
  the canonical classes, the latter extending H-projectivity and quasi-compactness.
  The current source was obtained with `scompile.py --source`, since the older checkout
  lacks this extracted module. Its finite-coordinate form is equivalent to the node's
  integer-coordinate convention, including the empty-source case explained in the proof.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`, `pullback.lift`:
  the chosen fibre product and universal-property construction underlying projective space.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`,
  `AlgebraicGeometry.ProjectiveSpace`, `ProjectiveSpace.over`,
  `ProjectiveSpace.isPullback_map`, `ProjectiveSpace.liftBaseChange`,
  `ProjectiveSpace.liftBaseChange_over`: the recorded projective-space construction,
  its structure projection and canonical pair.
- The proof-only dependency `Sheaf.AlgebraicGeometry.ClosedImmersionProducts`,
  `AlgebraicGeometry.closedImmersion_comp_products_and_finiteType_openImmersion`,
  is imported without `public`. All other recorded proof dependencies are in the imported
  proper, closed-immersion, separated, finite-type and projective-space modules.

Edge cases checked mathematically before writing:

- `N = ∅`: projective space is empty, so a map `i` forces `X'` empty; surjectivity
  of `π` forces `X` empty. Every conclusion remains valid. No nonempty coordinate
  or nonempty scheme hypothesis excludes this case.
- One coordinate: this is projective zero-space; the conclusions and canonical lift remain valid.
- Empty `S` and identity `π`: the canonical maps and both proper/projective assertions retain
  their ordinary meanings. Nothing requires a nontrivial modification.
- Nonreduced schemes and arbitrary characteristic: the statement uses scheme-theoretic
  closed immersions, with no reduction, field or characteristic restrictions.
- Non-Noetherian qcqs bases are included; no finite-presentation or Noetherian premise was added.
- The one explicitly bound universe `u` matches the coordinate set and schemes of the
  recorded dependency, and works for every universe. There are no auto-bound implicits.

Searches for an existing whole statement (2026-10-17 UTC):

- `msearch.py leanfinder`: “A proper morphism and a proper surjection with an immersion
  into projective space give closed immersions and projective morphisms”. Eight hits:
  `Proj.instIsProperToSpecZeroOfFiniteTypeSubtypeMemOfNatNat`, `IsProper`,
  `Scheme.Hom.isProperMap`, `IsProper.toUniversallyClosed`,
  `IsClosedImmersion.of_surjective_of_isAffine`, `Proj.instUniversallyClosed...`,
  `IsClosedImmersion.instIsMultiplicativeScheme` and
  `instUniversallyClosedOfIsClosedImmersion`. None states this whole conclusion.
- `msearch.py loogle`: `AlgebraicGeometry.IsProper, AlgebraicGeometry.IsClosedImmersion`.
  Two hits, `IsClosedImmersion.iff_isProper_and_mono` and
  `IsClosedImmersion.eq_proper_inf_monomorphisms`, neither the Chow statement.
- `msearch.py leansearch`: “Proper surjection and immersion into projective space imply
  projectivity and closed immersion over source scheme”. Eight hits on immersion and
  closed-immersion constructors/criteria; none the requested statement.
- `msearch.py grep`: `IsClosedImmersion.*lift|IsProjective|chow` in Mathlib
  `AlgebraicGeometry`: twelve hits on generic lifts, graphs and immersion criteria;
  no whole statement.
- Direct `rg` of upstream `WeilConjectures` and side `lean/Sheaf` for
  `chow.*closed|closed.*chow|chow.*projective|det-chow-projective-closed-immersions`,
  then `ChowModification|isClosedImmersion_toProjectiveSpace|IsProjective.*π|IsProjective.*pi|chow.*embedding`.
  The relevant candidates were read: upstream `ChowModification` is a selected modification
  over a Noetherian base, and `ChowModification.isClosedImmersion_toProjectiveSpaceSource`
  is only its selected closed embedding. The side theorem
  `chow_relative_ample_geometric` has coordinates `ULift (Fin (m+1))` only, and states
  four of the conclusions, without the composite properness or explicit projection identity.
  It therefore does not state the whole finite-set version, notably the empty-coordinate case.
- Direct `rg` for the chosen full theorem name in Mathlib, upstream, side sources and
  `dag/lean_names_upstream.json`, and `grep -rn` for this blueprint id in upstream:
  no existing declaration with this name or exact blueprint binding.

No statement dispute or node fault was found. Compilation and delivery preflight are run
through the prescribed wrappers; the only postponed proof is the named theorem above.

## Second reading by Q105

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
