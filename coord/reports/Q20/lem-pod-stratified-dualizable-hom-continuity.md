## Worker report

The module `Sheaf.Paper.StratifiedDualizableHomContinuity` states the original node,
without a statement correction. The primary theorem is
`AlgebraicGeometry.ProEtale.stratified_dualizable_hom_continuity`.
Its comparison lives in `ModuleCat (condensedScalarRing Λ.X)`, so `IsIso` is
an isomorphism of the required scalar modules, including linearity of the inverse.
All five theorem proofs are `sorry`; definitions and instances contain real data.
The theorem docstrings supply the natural-language proofs.

Hypothesis and clause correspondence:

- Scheme Y: `(Y : Scheme.{u})`.
- Quasi-compact: `[CompactSpace Y]`, with no separation axiom included.
- Quasi-separated: `[QuasiSeparatedSpace Y]`, equivalent to quasi-separatedness
  of the terminal scheme map by the recorded Mathlib dependency.
- Arbitrary commutative condensed ring: `(Λ : Profinite.CondensedRing.{u})`
  and `[IsCommMonObj Λ.X]`. No topological presentation is assumed.
- Pulled-back coefficient B: `condensedRingObj Λ.X Y`, the underlying object
  of the recorded `coefficientRing Y Λ`.
- Small pro-etale site: `Scheme.ProEt.topology Y`, on `Y.ProEt`.
- Module sheaves: the published internal-module presentation
  `Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ.X Y)`.
  This is the module-sheaf category used by the recorded relative derived tensor.
  Its sectionwise identification with `ringedSiteModules` is the existing
  `InternalAbelianSheafModule.sectionModuleEquivalence`; no category is redefined.
- Ordinary unbounded derived category: `DerivedCategory` of that exact category.
  No completion, bounded subcategory, or constructible-target subcategory appears.
- Ordinary relative derived tensor: the imported ModuleObject.Derived.Hom and
  Tensor framework provides its fixed monoidal structure, used by `HasRightDual`.
- Finite scheme stratification: the existential `S : Y.FiniteLocallyClosedStratification`
  inside `hK`. It contains the finite index `Fin S.n`, locally closed subsets,
  pairwise disjointness, covering, schemes, immersions and their precise images.
- Constructible strata: `∀ i, Topology.IsConstructible (S.stratum i)`, explicitly
  added to the recorded stratification notion, which itself does not assume this.
- Dualizability on each stratum: `∀ i, Nonempty (HasRightDual
  ((CondensedRing.upperStar Λ.X (S.immersion i)).mapDerivedCategory.obj K))`.
  `HasRightDual` gives an object D and `ExactPairing K D`: coevaluation
  `1 → K ⊗ D`, evaluation `D ⊗ K → 1`, and both contraction identities with
  the specified associators and unitors. This is the exact orientation in the node.
- Small filtered I: `{I : Type (u + 1)} [SmallCategory I] [IsFiltered I]`.
  This is the established size convention for the pro-etale module framework;
  filteredness includes nonemptiness and equalization of parallel maps.
- Diagram of integer cochain complexes: the binder `C : I ⥤ CochainComplex ... ℤ`.
- One common strict lower bound: `(a : ℤ)` and
  `ha : ∀ (i : I) (j : ℤ), j < a → IsZero ((C.obj i).X j)`.
  This bounds actual terms, without replacing the hypothesis by a homology bound.
- Termwise colimit and its original legs: `colimit C` and `colimit.ι C i`, using
  the existing cochain-complex colimit instance, computed degreewise in module sheaves.
  There is no colimit universal property assumed in the ordinary derived category.
- Q and integer shift: `DerivedCategory.Q ⋙ shiftFunctor _ r`, for `(r : ℤ)`.
- The module Hom diagram: `stratifiedShiftedLinearHom R K r` is precisely this
  composite followed by `linearCoyoneda R _ |>.obj (op K)`.
- Canonical comparison: `stratifiedHomComparison` is `colimit.desc` of the image
  of `colimit.cocone C` under this exact functor. Its maps are not arbitrary.
- Specified formula `[u_i] ↦ Q(ι_i)[r] ∘ u_i`:
  `stratifiedHomComparison_leg`, with Lean composition written in diagram order.
- Isomorphism over Γ(*,Λ): the main conclusion is `IsIso` of this module map.
  `condensedScalarRing Λ.X` is the already recorded reconstructed ring at the
  terminal profinite set, literally Γ(*,Λ), rather than Γ(Y,B) or a special field.
- Naturality in K: `stratifiedHomComparison_source_naturality` states the square
  induced by every `f : K' ⟶ K`, with `stratifiedHomPrecomp` obtained from
  `linearCoyoneda.map f.op`. This holds even without dualizability restrictions.
- Naturality in diagram morphisms: `stratifiedHomComparison_diagram_naturality`
  states the square for every natural transformation `α : C ⟶ E`, using
  `colimMap α` for the actual colimit map. The generic theorem has no bound
  assumption, so diagrams with different common bounds are included.
- No constructibility condition on C, no Noetherian hypothesis, and no
  finite-dimensional hypothesis are present anywhere in the main signature.

The module constructs the missing canonical scalar packaging as helpers of this
node, under the brief's authorization for helpers belonging to the same notion.
`stratifiedHomScalarSection` sends a scalar through the constant-sheaf adjunction
(on the unit ULift ℤ), then through the unit comparison and map of `upperStarFromPoint`.
`stratifiedHomScalarCenter` reuses `Mod.qbar_scalarNatEndo` and `qbar_derivedCenter`,
which are general constructions despite their historical names. Their real data
are the regular-module action, extension to complexes, and localization.
`stratifiedHomScalarCenter_laws` postpones the ring-law proofs needed for the scalar
linearity already asserted by this node. `stratifiedHomScalarMap` has exactly
that fixed function as `toFun`; no arbitrary or existentially chosen map is used.
`stratifiedHomLinear` applies Mathlib's `Linear.ofRingMorphism` to that ring map.
The scalar ring laws are the scalar-structure portion of this node, not an
independent mathematical input or a stronger hypothesis on its main theorem.

Dependency declarations read and used:

- `Mathlib.Topology.Defs.Filter`: `CompactSpace`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`: `QuasiSeparated` and
  the equivalence with `QuasiSeparatedSpace` for a scheme's terminal map.
- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `Scheme.ProEt.topology`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`: `coefficientRing`,
  `coefficientRing_X`, `condensedRingObj`, `upperStarFromPoint` and its monoidality.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`:
  `CondensedRing.derivedHom`, with the recorded ordinary relative monoidal structure.
- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`:
  `Scheme.FiniteLocallyClosedStratification`, including every field.
- `Mathlib.Topology.Constructible`: `Topology.IsConstructible`.
- `Mathlib.CategoryTheory.Monoidal.Category`: `MonoidalCategory`;
  `Mathlib.CategoryTheory.Monoidal.Rigid.Basic`: `ExactPairing`, `HasRightDual`.
- `def-weil-size-convention` is a convention; explicit universe u, coefficient
  size u+1, and small diagram size u+1 render it. The existing framework supplies
  the canonical derived localization size; no equality of site universes is imposed.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `Cocone`, `colimit`, `colimit.ι`,
  `colimit.desc`; `Mathlib.CategoryTheory.Filtered.Basic`: `IsFiltered`.
- `Mathlib.Algebra.Homology.HomologicalComplex`: `CochainComplex`.
- Additional already landed `def-zl-condensed-scalar-realization` is appended to
  stmt_deps to cite the exact `condensedScalarRing` from
  `Sheaf.AlgebraicGeometry.CondensedScalarRealization`; its signature and full
  docstring were read. This adds no new node and changes no statement text.

All proof-dependency modules with recorded declarations are imported without
`public`, including the Hom cohomology ladder, refinement, pullback locality,
closed monoidal structure, K-flat resolutions, filtered tensor, internal-Hom
bound, recollement, qcqs pushforward continuity, ringed open-closed operations,
internal-Hom formulas, global sections, and signed right shift. The remaining
proof dependencies have no recorded project module and need no new construction
to type this stage-2 statement.

Source and edge cases:

Read the supplied Hemo--Richarz--Scholbach PDF using pdftotext, including Lemma 5.3
and its full proof on page 14. Its bounded-below internal-Hom and final global-Hom
assertions give exactly this strict-diagram specialization, in every cohomological
integer degree. The source explicitly uses boundedness of constructible sources.

Checked empty Y (zero module category and empty finite partition allowed), zero K,
zero targets, the zero coefficient ring, empty strata and rank-zero duals, arbitrary
negative or positive a and r, and singleton or non-posetal filtered categories.
An empty I is correctly excluded by IsFiltered, which is part of the stated input.
The uniform bound is shared by all i; no individual bounds replace it. Γ(Y,B) need
not equal Γ(*,Λ): the scalar action explicitly pulls back the latter. No flatness
of Λ, finite cohomological dimension or Noetherianity is used in the signature.

Searches for existing notions/statements (2026-10-21):

- msearch.py leanfinder: "For a qcqs scheme and stratified dualizable condensed
  sheaf K, Hom(K,-) commutes with filtered colimits of uniformly bounded below
  cochain complexes". Eight hits: underived condensed AB5/exactness, light
  condensed monoidality and local finite presentability, no matching theorem.
- msearch.py loogle: "CategoryTheory.Preadditive.linearCoyoneda,
  CategoryTheory.Limits.colimit, CategoryTheory.HasRightDual". Zero hits; the
  first expected name was incorrect. Direct source search found the exact
  `CategoryTheory.linearCoyoneda` in Mathlib/CategoryTheory/Linear/Yoneda.lean.
- msearch.py grep: "Hom.*colimit|colimit.*Hom", subdirectory CategoryTheory.
  25 reported hits on general colimit universal properties and finite
  presentability; none is this geometric bounded-below continuity theorem.
- rg in lean/WeilConjectures for the item id: no matches.
- rg in lean/WeilConjectures and lean/Sheaf for stratified dualizability and
  Hom continuity: existing finite-free, locally finitely presented field,
  local-piece and qcqs-pushforward statements are narrower or different.
  Their helper interfaces were read; none states this arbitrary-ring theorem.
- rg in Mathlib/CategoryTheory for linearCoyoneda, linear structures and
  centers found the exact reusable linear Hom and central-action interfaces.
- rg in the project found `condensedScalarRing`, `Mod.qbar_scalarNatEndo`
  and `qbar_derivedCenter`; these existing definitions are reused, not copied.
- rg in dag/lean_names_upstream.json for the new helper prefixes: no clashes.

No STATEMENT-DISPUTED flag, unusable dependency record, or statement correction.
No new definition nodes or dependency modules are needed.

Validation: scompile.py compiles both the sandbox and final library module
cleanly, under the default 60-second per-file limit. Only scompile.py was used;
no live source edit or global build was performed.

## Second reading by Q20

The dispatcher explicitly prohibits starting another agent. This is a separate
self-check, not a claimed independent reading; the maintainer's independent
review remains the delivery review described in the brief.

Reopened the node and the final Lean file. `hK` uses the existing finite
stratification and adds exactly constructibility and right dualizability of each
derived restriction. Its ExactPairing has evaluation D⊗K and coevaluation K⊗D,
matching the original orientation. The category is the ordinary uncompleted
ModuleObject derived category. The lower-bound condition is termwise and uniform.
The comparison uses the original colimit, not its good truncation. Its leg theorem
has Q(ι)[r] after u. The scalar action is Γ(*,Λ) pulled back by the actual
monoidal inverse image; the laws only discharge structure proofs for that fixed
data. The two naturality statements are equalities in the same module category.
The main theorem's IsIso thus gives the precise module isomorphism asserted.
No hypothesis on diagram constructibility, Noetherianity or dimension was added.
All declaration variables and universes are bound, all postponed proofs are named,
and all definitions contain actual data. No mismatch was found on this reading.
