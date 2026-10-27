## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousLineBundleSections`
states `AlgebraicGeometry.exists_homogeneousLineBundle_sections`, with its sole
proof `sorry`. The module
`Sheaf.AlgebraicGeometry.GroupScheme.AssociatedCharacterLineBundle` defines the
missing presentation of the associated quotient and its section sheaf. Its data
are explicit constructions and structure fields; it contains no postponed proof
and makes no arbitrary choice of a bundle, an action, or a comparison map.

The existing node statement is unchanged. Only `lean` and permitted additions to
`stmt_deps` change. There is no statement dispute or source correction.

Hypotheses, individually:

- `F : Type u`, `[Field F]`, `[IsAlgClosed F]` give the algebraically closed field.
- `G : Grp (Over (Spec (.of F)))` gives the group scheme, and
  `hG : ReductiveTorusCentralizer.IsReductive G` is exactly the reductivity
  predicate used by the recorded Borel-pair dependency, including smoothness,
  connectedness, affineness, finite type and absence of the unipotent radical.
- `T`, `B`, `iT`, `iB`, `hT`, `hTs`, `hB`, `j`, `hj` give the fixed split maximal
  torus and Borel containing it. The split witness allows rank zero. `hB` is the
  existing Borel predicate, and `hj` fixes the inclusion of T through B.
- `Q`, `π`, `hQ`, `hQft`, `hQqc`, `hπf`, `hπs`, `hπi`, `hπt` unpack exactly the
  quotient/torsor conclusion of `reductive_borel_pair_structure`: proper finite
  type Q, flat surjective π, right B-invariance and the cartesian kernel-pair
  square with arrows `(g,b) ↦ g` and `(g,b) ↦ gb`. These specify the Q and π
  mentioned as coming from that dependency, not an additional condition on G.
  Finite type is `LocallyOfFiniteType` plus `QuasiCompact`, as in that signature.
- `χ : B ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)` is any group-scheme
  character, not a character of abstract F-valued points.

Conclusions, clause by clause:

- `∃ ψ, ψ.hom.hom = χ.hom.hom⁻¹` exposes the inverse character required by
  Milne's convention. This is a conclusion with its actual underlying map
  pinned to pointwise group inversion. It is neither an extra hypothesis nor
  an arbitrary character. The target then uses the existing positive-convention
  `RhoSection.sectionModule G B iB ψ 1`, which says precisely
  `f(gb) = χ(b)⁻¹ f(g)` over every commutative F-algebra.
- `∃ P : AssociatedCharacterLineBundle.Presentation G B iB Q π χ` supplies the
  quotient total space `P.V`, bundle projection `P.projection`, quotient atlas
  `P.quotientMap`, sheaf `P.L` and specified pullback trivialization.
- `P.quotient_relation` is exactly the right action
  `(g,z)b = (gb,χ(b)⁻¹z)`: equality of quotient images is equivalent to that
  relation on every scheme-valued point. Together with its flat, surjective,
  quasi-compact atlas it specifies the fpqc sheaf quotient, rather than the
  potentially smaller pointwise orbit set on F-points.
- `P.sectionRepresentation` is a natural equivalence, over every `x : S ⟶ Q`,
  between sections of `x^*P.L` and maps `S ⟶ P.V` over x.
  `sectionRepresentation_natural` fixes arbitrary base change, and
  `sectionRepresentation_coordinate` fixes this equivalence to `[g,z]` in the
  specified trivialization. With invertibility this is the usual geometric line
  bundle of L. No extra vector-bundle notion is redefined.
- `P.baseAction`, `P.totalAction` are `ModObj` structures: algebraic morphisms
  with identity and associative action laws. `projection_equivariant` makes
  the projection equivariant. `baseAction_coordinate` and
  `totalAction_coordinate` fix them to `π(sg)` and `[sg,z]`. Keeping z unchanged
  implies fibrewise linearity; this is the natural homogeneous structure in
  Milne 18.13, not an arbitrary action on an abstract vector space.
- `P.L.IsInvertible` is Zariski-local isomorphism with the structure sheaf,
  exactly `Scheme.Modules.IsInvertible` from the recorded module.
- `Scheme.Modules.isCoherent Q.left P.L` is quasi-coherent plus finite
  presentation. This is equivalent to the node's full coherent-sheaf condition
  here: Q is proper of finite type over a field and therefore locally
  Noetherian. The warning in the upstream definition on arbitrary non-Noetherian
  schemes does not apply to Q. No Noetherian hypothesis is added.
- `e : sections Q P.L ≃ₗ[F] RhoSection.sectionModule ... ψ 1` is the stated
  F-linear identification. `sections` restricts scalars along the actual map
  `F → Γ(Q,O_Q)`. `RhoSection.Coordinate G.X` is the actual coordinate algebra,
  not an abstract replacement or a set of arbitrary point functions.
- The equation `∀ σ, (e σ).val = pullbackCoordinate π ... σ` fixes e to pullback
  followed by the specified trivialization. That helper uses the existing
  canonical module-pullback unit, then the explicit preimage-top transport and
  the actual sheaf isomorphism; no free linear map replaces this operation.
- The final quantified identity is equivariance written directly on geometric
  sections: pull σ to `(s⁻¹g)π`, represent it in the total space, then apply s.
  The result is `[g, ev_(s⁻¹g)(e σ)]`. It is literally `(sf)(g)=f(s⁻¹g)`, expressed
  without assuming an unspecified representation. S ranges over every F-scheme,
  so this includes every F-algebra and the universal group point. Together with
  the geometric G-action it records algebraic equivariance, not only the action
  of G(F). Addition and scalar extensions are fixed by the local coordinate
  normalization of the representing equivalence.

Dependencies read and reused:

- `Field` (`Mathlib.Algebra.Field.Defs`) and `IsAlgClosed`
  (`Mathlib.FieldTheory.IsAlgClosed.Basic`); no closure of F is unnecessarily
  chosen. The algebraic-closure dependency's record explicitly includes this
  algebraic-closedness class.
- `CategoryTheory.GrpObj`, `Grp`, `Grp.homMk`, and the pointwise group structure
  on maps into a group object (`Mathlib.CategoryTheory.Monoidal.Grp`), with
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`' scheme interpretation.
- `AlgebraicGeometry.reductive_borel_pair_structure`
  (`Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure`), whose full
  signature and proof docstring were read. The theorem's quotient hypotheses
  are its existing quotient conclusion, without choosing a different model.
- `AlgebraicGeometry.RhoSection.Coordinate` and `sectionModule`
  (`Sheaf.AlgebraicGeometry.RhoSectionModuleData`, node
  `def-sfb-rho-section-module-data`), read after the search found that newly
  landed definition. Its `evaluate` and `characterValue` are reused inside
  sectionModule; no second semi-invariant-submodule definition is delivered.
- `StandardGroupSchemes.additive`, `multiplicative`, `affine` and `map`
  (`Sheaf.AlgebraicGeometry.StandardGroupSchemes`); `linePoint` uses the existing
  `algΓAlgSpecAdjunction` and Polynomial.aeval, and inverseCharacter reads the
  existing Laurent coordinate after inversion.
- `Scheme.Modules.IsInvertible`
  (`WeilConjectures.AlgebraicGeometry.Modules.Invertible`),
  `Scheme.Modules.isCoherent`
  (`WeilConjectures.AlgebraicGeometry.Modules.Coherent`), canonical Mathlib
  `Scheme.Modules.pullback` and `pullbackComp`, upstream `pullbackSection` and
  `pullbackObjUnitIso`, and `CategoryTheory.ModObj`. These are their existing
  mathematical constructions, not private copies. This presentation uses the
  canonical Mathlib module-pullback functor already used by IsInvertible;
  it introduces no second pullback functor.

Proof-only imports retain the available plan: upstream Descent, FpqcTensorSections,
Mathlib Gluing, Fpqc, FiniteType, prime-spectrum Noetherian and NoetherianSpace.
The proof dependency `lem-trf-proper-field-invertible-coherent` has no recorded
Lean declaration, so has no import. No proof is attempted. The natural-language
proof in the theorem docstring gives all six node steps and their dependencies.

Edge cases checked before finalization:

- The trivial character gives invariant functions and the trivial associated
  bundle; no nontriviality or nonzero-section hypothesis is imposed.
- A torus has B=G and Q a point; the inverse character and left regular action
  have the correct signs. For SL₂, χ and χ⁻¹ are not silently interchanged.
- Zero global-section spaces and zero sections are allowed. No basis, positive
  dimension, dominant-character or nonvanishing assumption is present.
- Arbitrary characteristic, including characteristic two, is retained. No
  differentiation of a character is used to detect it.
- Nonreduced test algebras, the zero algebra and empty test schemes are included.
  Every scheme and field uses the explicit universe u; test schemes live in
  `Over (Spec (.of F))`, whose objects include all affine test algebras of that
  universe. The all-scheme formulas are equivalent to the algebra formulas by
  restriction to affine opens, not by restriction to F-points.
- The zero coordinate is represented by the zero bundle section. Every action,
  projection and comparison is fixed by the atlas equations on all test schemes.

Searches made:

- msearch LeanFinder: "Sections of a homogeneous line bundle on a flag variety
  equal regular functions on an algebraic group satisfying right character semi
  invariance". Eight hits concern continuous cohomology or abstract/finite-group
  induction, not the algebraic flag quotient or this section realization.
- msearch LeanSearch: "An associated character line bundle on a quotient group
  scheme is represented by the sheaf of sections of an invertible module".
  Eight hits include PicardGroup and Scheme.Modules definitions, but no associated
  character quotient or its normalized section/action comparison.
- msearch Loogle: `SheafOfModules.IsInvertible, GrpObj, ModObj, Scheme.Modules`
  has no match (first name is not an identifier in pinned Mathlib). A follow-up
  uses the actual `CategoryTheory.GrpObj` and `Scheme.Modules.IsInvertible` names;
  no existing statement of this theorem was found.
- msearch grep: `AssociatedBundle|homogeneousLine|semiInvariant` in
  Mathlib/AlgebraicGeometry returns zero hits. Direct rg in WeilConjectures and
  Sheaf found no associated-character bundle presentation. The direct broad
  semi-invariant search did find `def-sfb-rho-section-module-data`; its module
  was opened and reused. The exact item-id search in WeilConjectures returns
  no existing theorem.
- DAG searches for associated/homogeneous line bundles found consumers, general
  vector bundles and the rho-section definition, but no quotient presentation.
  `tools/blueprint_refs.py search "homogeneous line bundle"` returned zero
  blueprint nodes; `ancestor` returned None, preserved in the new record.
- The actual Milne PDF was read at printed pp.389--390, Definition 22.21 p.468,
  and the proof of Theorem 22.48 p.479. Its inverse-character action and all-algebra
  section equation agree exactly with the node. Temporary text is sandbox-only.

Compilation: both delivered files compiled cleanly, separately in dependency
order, using scompile.py against the published live build. The last run reported
4.4/5.8 seconds for the definition and 5.5/8.2 seconds for the theorem's sandbox
and library checks. All variables/universes are explicit; autoImplicit is false.

## Second reading by Q41

I reread the node, both completed files and the new definition record directly.
This is a second pass by the dispatched worker; no separate agent was started,
as the dispatcher explicitly forbids that. The maintainer's independent review
remains the independent reading of this delivery.

The key mismatch caught on this pass was a prospective duplicate of the newly
landed semi-invariant module. It was removed: the conclusion now uses
RhoSection.sectionModule with exponent one and an explicitly fixed inverse
character. I also removed a prospective extra postponed helper theorem by
expressing the inverse character as part of the main theorem's existence
conclusion. The definition module now contains no sorry.

I checked every hypothesis against the source and the recorded quotient
signature: algebraic closedness, reductivity, the given split torus/Borel pair,
all torsor equations and an arbitrary character are retained. The quotient
relation has the inverse scalar; the natural section equivalence agrees with
that relation in the given trivialization. The actions are scheme morphisms
with their laws and the correct atlas formulas. The linear equivalence lands
in the actual all-algebra semi-invariants and is pinned to pullback, not merely
asserted abstractly. The final formula acts on geometric sections at s⁻¹g,
then translates to g with unchanged scalar coordinate. Invertibility uses the
existing Zariski definition; coherence is equivalent to the full kernel
condition because this Q is Noetherian. No remaining clause mismatch was found.
The item statement, source, proof, proof_deps, status and unit are unchanged.

## New nodes

`def-sfb-associated-character-line-bundle` defines the presentation needed to
state the existing node: actual quotient scheme and atlas, exact B-orbit relation,
section-sheaf representation natural on every scheme over Q, specified pullback
trivialization, and geometric left actions fixed to left multiplication. It
also owns the explicitly constructed coordinate and pullback helpers. Source:
Milne Section 18c pp.389--390 and Theorem 22.48 p.479. The three kinds of search
are recorded verbatim in mathlib_searches; direct source and DAG searches are
recorded there as well. Existing group objects, actions, coordinate algebras,
semi-invariants, module pullback and invertibility are reused. A general vector
bundle atlas does not specify this associated quotient, and the landed
rho-section node supplies functions but no quotient or geometric action.
