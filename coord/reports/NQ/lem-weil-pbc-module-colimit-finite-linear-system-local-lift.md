## Worker report

States `SheafOfModules.colimit_finite_linear_system_local_lift` in
`Sheaf.Topology.ModuleColimitFiniteLinearSystemLocalLift`. Its only proof is `sorry`.
No definitions, dependency repairs, new nodes, statement corrections, or disputed
statements are needed. The original node is preserved except for its Lean record.

Hypothesis and clause correspondence:

- The topological space is `{X : Type u} [TopologicalSpace X]`.
- The commutative ring sheaf is
  `O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{max u r}`.
  `sheafCompose ... (forget₂ CommRingCat RingCat)` is its canonical underlying
  ring sheaf, retaining its exact rings and restriction maps. The coefficient
  universe contains the space universe so that the existing limit-preserving
  forgetful functor supplies this sheaf composition without an extra assumption.
  All data can be placed in a common universe; no mathematical size or topology
  condition is imposed.
- The module category is the recorded `CategoryTheory.ringedSiteModules.{u}`
  applied to that ring sheaf, transparently Mathlib's `SheafOfModules`.
- The nonempty directed preordered set is `{I : Type u} [Preorder I]
  [IsDirected I (· ≤ ·)] [Nonempty I]`. Antisymmetry is not required.
  The module and index universes use the project's common-universe convention.
- The diagram is `F : I ⥤ ...`. Its functorial maps along `homOfLE` give exactly
  the stated module-linear transition maps and their composition laws.
- The supplied colimit and its specified legs are `c : Cocone F` and
  `hc : IsColimit c`. Thus `c.pt` is the node's F and `c.ι.app i` is its c_i;
  no special choice of colimit or change of the legs is made.
- The open is `W : Opens X`; the nonnegative integers are `m n : ℕ`.
- The coefficient matrix is `a : Fin m → Fin n → O.obj.obj (op W)`.
  The section tuple is `s : Fin n → c.pt.val.obj (op W)`.
- Every assumed equation is exactly
  `hs : ∀ k : Fin m, ∑ r : Fin n, a k r • s r = 0`.
  The scalar action is the existing module-sheaf action over O(W).
- The pointwise assertion is `∀ x : X, x ∈ W → ...`.
- Its witnesses `V : Opens X`, `hVW : V ≤ W`, and `x ∈ V` say
  precisely that V is an open neighbourhood of x contained in W.
- The single witness `i : I` and the tuple
  `t : Fin n → (F.obj i).val.obj (op V)` give all lifts at one stage.
- The first conclusion is
  `(c.ι.app i).val.app (op V) (t r) =
    c.pt.val.map (homOfLE hVW).op (s r)` for every r: the specified
  colimit map sends t_r to the restriction of s_r.
- The second conclusion is
  `∀ k : Fin m, ∑ r : Fin n,
    O.obj.map (homOfLE hVW).op (a k r) • t r = 0`:
  every coefficient is restricted along exactly V ⊆ W, and all m equations
  hold in the same module F_i(V).
- There is no compactness, separation, coherence, or injectivity hypothesis.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedSiteModules`,
  `CategoryTheory.ringedSiteModules`: the recorded category abbreviation;
  `Mathlib.Algebra.Category.ModuleCat.Sheaf`, `SheafOfModules`,
  `SheafOfModules.Hom`, and `Mathlib.Algebra.Category.ModuleCat.Presheaf`,
  `PresheafOfModules.obj`, `PresheafOfModules.map`, and
  `PresheafOfModules.Hom.app`: sections, restriction and linear components.
- `Mathlib.CategoryTheory.Limits.HasLimits`, `CategoryTheory.Limits.colimit`;
  the node's recorded `CategoryTheory.Limits.Cocone` and
  `CategoryTheory.Limits.IsColimit` (defined in Cones and IsLimit) are the
  actual interface for a supplied colimit. Their full structures and the
  generated colimit declaration's source and docstring were read.
- `Mathlib.CategoryTheory.Filtered.Basic`, `CategoryTheory.IsFiltered`:
  nonempty directed preorders give precisely the filtered index categories
  used by the proof, with unique parallel arrows.
- Proof import `Sheaf.CategoryTheory.ModuleDirectedColimitUnderlyingSets`,
  `SheafOfModules.underlying_directed_colimit_isColimit`.
- Proof import `Mathlib.CategoryTheory.Sites.Limits`,
  `CategoryTheory.Sheaf.sheafifyCocone` and
  `CategoryTheory.Sheaf.isColimitSheafifyCocone`, from the dependency's
  `mathlib_match` (no dependency Lean record is necessary).
- Proof import `WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal`,
  `CategoryTheory.sheafification_sections_local`.
- Proof import `Mathlib.CategoryTheory.Limits.Types.Filtered`,
  `CategoryTheory.Limits.Types.jointly_surjective`,
  `CategoryTheory.Limits.Types.FilteredColimit.isColimit_eq_iff`, and
  `CategoryTheory.Limits.Types.FilteredColimit.isColimit_eq_iff'`.
  These are the elementwise dependency's recorded Mathlib matches.

The proof docstring records all five DAG steps: compare the specified cocone to
presheaf-colimit sheafification; lift each section locally; intersect and advance
the finite tuple; locally kill each linear-relation error; intersect again and
advance to a common index. Sources read: Stacks `sheaves.tex`, Tag 009F,
statement and proof (lines 3444 onward), and `modules.tex`, Tag 0GMV,
statement and finite-relation proof (lines 3759 onward). The former's compactness
assumptions concern assembling data over the entire open, not lifting near one point.

Edge cases checked before writing: n = 0 leaves an empty tuple and every sum is
zero; take V = W and any index, available by Nonempty I. With m = 0 there are no
relations, and the result is simultaneous local lifting of a finite tuple.
With both zero the same choices work. If W or X is empty the pointwise conclusion
is vacuous. The zero ring and zero module cause no obstruction. Noninjective
transitions are allowed; relation errors are killed only after shrinking and
advancing. Directed preorders with equivalent distinct indices are allowed.

Searches, using the prescribed msearch.py wrapper (2026-10-23):

- LeanFinder: "A finite tuple of sections satisfying linear equations in a directed
  colimit of module sheaves lifts locally to one stage". Eight hits concern
  `SheafOfModules.Presentation.isColimit`, `Presentation.map_generators_I`,
  generating sections and local finite-type generators. Read the presentation
  cokernel signature and finite-type interface: these do not assert lifting a
  finite solution at a common stage near each point.
- Loogle: `SheafOfModules, Matrix`. No hits.
- Mathlib grep in Algebra/Category/ModuleCat/Sheaf:
  `[Cc]olimit.*([Ll]ift|[Ee]quation)|([Ll]ift|[Ee]quation).*[Cc]olimit`.
  No hits.
- LeanSearch: "Finite homogeneous linear equations in sections of directed colimits
  of module sheaves lift near each point to one stage". Eight hits concern
  `DirectLimit.Module.lift`, `ModuleCat.directLimitIsColimit`, related algebraic
  direct-limit maps, and existence of scheme-module colimits. None is the local
  finite-equation statement for arbitrary module sheaves.
- rg over WeilConjectures and Sheaf for `finite_linear`, `linear_system`,
  `colimit.*lift`, and `lift.*colimit`, and rg for the exact blueprint id in
  WeilConjectures. No exact statement exists. Read the nearby
  `WeilConjectures.Topology.Sheaves.NoetherianColimit` local section and equality
  lemmas (abelian sheaves, one section at a time),
  `WeilConjectures.AlgebraicGeometry.ModuleUnitLocalSupport` local lift helper
  (private, over schemes, one section), and
  `Sheaf.CategoryTheory.Sites.FpStalkRealization` matrix lift (private, ring
  colimit coefficients). None states this result or replaces it verbatim.
- Checked the proposed declaration name in Mathlib, WeilConjectures, and Sheaf:
  no collision.

Validation: scompile.py compiled the sandbox module and its actual library module
separately, with the exact delivery header/import visibility. Both are clean.
`autoImplicit` is false and every universe and variable is explicitly bound.
The node's Lean signature is extracted verbatim from the delivered theorem.

## Second reading by NQ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
