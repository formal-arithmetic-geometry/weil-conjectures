## Worker report

The module `Sheaf.AlgebraicGeometry.BertiniSmoothMember` states
`AlgebraicGeometry.exists_open_smooth_bertiniMember`, with proof `sorry`, and supplies three
real-data helpers for the exact coefficient point, section, and section-family conversions.
Source read: `literature/stacks-project/varieties.tex`, Situation 0FD3 and Lemma 0FD6,
lines 10908–11060 (including the whole proof); the current blueprint ancestor's proof,
`main-20261015/blueprint/sec-deligne-laumon-general/sk-i-dl-general-real/` followed by
`lem-zl-bertini-finite-cover-curve.proof.md`, uses exactly Tag 0FD6 on X minus S.
There is no statement correction and no disputed assertion.

Hypotheses and clauses, checked individually against the node:

- A field k is `{k : Type u} [Field k]`.
- Y over k is the explicit structure map `f : Y ⟶ Spec (CommRingCat.of k)`.
  It is explicit because base change and the recorded projective-map constructor use it.
  `[Smooth f]` is precisely smoothness of Y over k, with no properness, perfection,
  nonemptiness, integrality, or characteristic restriction.
- The invertible O_Y-module is `(L : Y.Modules) [L.IsInvertible]`, using the recorded
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`.
- The finite-dimensional vector space is `V` with `AddCommGroup V`, `Module k V`, and a
  `Module.Basis I k V` for a finite index type `[Fintype I]`. This is an arbitrary finite
  basis, rather than a chosen restricted vector space. Enumerating I identifies it with
  the node's basis of length r = card I. Empty I is permitted. Neither a nonzero vector
  space nor an injective ψ is assumed.
- The k-linear ψ is `(ψ : V →+ Γ(L, ⊤))` together with `_hlinear`. Additivity is bundled;
  `_hlinear` says ψ(c v) = (f^*c) ψ(v) for every c and v. Here `ΓSpecIso.inv` followed by
  `f.appTop` is the actual canonical k-action. No arbitrary module structure is supplied.
  Top-open sections are canonically the global sections. `bertiniSectionFamily` turns
  them into `L.sections` through the existing `homOfGlobalSection` and `unitHomEquiv`.
- Generation of the image of ψ is `hgen : Epi (L.freeHomEquiv.symm
  (bertiniSectionFamily L (fun i ↦ ψ (b i))))`. Since b is a basis and ψ is linear,
  its basis images generate exactly the same sheaf as its entire image. This is the
  recorded generating-sections interface, with the same Epi convention.
- The associated morphism is the recorded `ProjectiveSpace.homOfGeneratingSections I f L`
  on exactly that same family; its `IsImmersion` instance is precisely the node's
  immersion hypothesis. The projective space has homogeneous coordinates indexed by
  the basis I, so it is P(V), with the convention of Stacks 01NE/01NF.
- The open U lives in `Spec (CommRingCat.of (MvPolynomial I k))`, exactly affine r-space
  over k in these basis coordinates. It is Zariski open by its type `.Opens` and has
  an explicit underlying-set `.Nonempty` conjunct.
- U is chosen BEFORE `∀ (K : Type u) [Field K] [Algebra k K] (a : I → K)`, so the same
  open works for every field extension and every tuple. All objects use the common
  arbitrary universe u; the extension-field quantifier has no independent smaller
  universe. No infinitude or algebraicity is imposed on K/k.
- `bertiniCoefficientPoint (k := k) a` is `Spec.map` of polynomial evaluation with
  coefficients `algebraMap k K` and variables sent to a. Range contained in U is
  exactly the condition that the K-point lies in U(K), including over non-rational
  residue points; no k-rational point in U is required.
- `pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))` is Y_K; its `fst` is the
  map to Y and its `snd` the structure map to Spec K. This is the pullback convention
  explicitly prescribed in the record of `def-pc-base-change`.
- `bertiniMemberSection` is the finite sum of `tensorSectionsUnit fst L (ψ (b i))`
  with coefficient `snd.appTop (ΓSpecIso.inv (a i))`. Thus it is the actual section
  ∑ a_i ψ(b_i) of the tensor pullback of L to Y_K. No universal family, map, or sheaf
  is an arbitrary input or a choice from a bare existence assertion.
- `homOfGlobalSection` renders that section as O_{Y_K} → L_K. Its recorded `zeroLocus`
  and `subschemeι` give exactly H_v = Z(ψ(v)) with its scheme structure. The conclusion
  `Smooth (subschemeι ≫ pullback.snd ...)` is precisely smoothness over K.

The helpers only expand constructions within this node's Situation 0FD3; they introduce
no independent notion and no postponed theorem. The theorem docstring carries all four
proof steps of the DAG: universal zero family and fibres; singular-locus bound; smoothness
on the complementary open and smooth base change; nonempty uniform open.

Dependency declarations used/read:

- Convention nodes `def-weil-pbc-scheme-conventions` and
  `def-weil-scheme-morphism-properties` have no declaration/module of their own. Their
  prescribed Mathlib leaves give `AlgebraicGeometry.Scheme`, `IsImmersion`, and `Smooth`.
  Read the full smooth signature from current `Mathlib.AlgebraicGeometry.Morphisms.Smooth`
  through `scompile.py --source`; immersion from `Morphisms/Immersion.lean`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`,
  `AlgebraicGeometry.Scheme.Modules.IsInvertible` (full signature and docstring read).
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators`,
  `SheafOfModules.GeneratingSections`, specifically its recorded `Epi (L.freeHomEquiv.symm s)`
  interface (full structure read).
- `WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus`,
  `AlgebraicGeometry.Scheme.Modules.Hom.zeroLocus`, returning `Y.IdealSheafData`; read its
  full docstring identifying a section with O_Y → L and its ideal with im(s-dual).
- `def-pc-base-change`: its record explicitly tells scheme-base-change citers to use
  `Limits.pullback`, `pullback.fst`, and `pullback.snd`. Its primary `moduleBaseChange`
  concerns a different clause (module pullback along a map between base schemes);
  it is not misapplied here. Read the entire current
  `WeilConjectures.AlgebraicGeometry.BaseChangeConventions` via `scompile.py --source`.
- Added the already recorded definition node
  `def-weil-pbc-morphism-to-projective-space-by-sections` to stmt_deps, as authorized
  for an existing landed notion. Its module
  `Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections` and declaration
  `AlgebraicGeometry.ProjectiveSpace.homOfGeneratingSections` are read and used exactly.
- Section pullback uses `Scheme.Modules.tensorPullback` and `tensorSectionsUnit` from
  `Sheaf.AlgebraicGeometry.EtaleTensorSections`, with the canonical tensor adjunction unit;
  no second module-pullback definition. `homOfGlobalSection` is reused from
  `WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator`.
- Proof dependencies already stated are available through the Smooth and Proper imports
  (`smooth_isStableUnderBaseChange`, source-local smoothness). The singular-locus bound
  has no recorded module yet and cannot be imported; its id stays in the proof docstring.

Edge cases checked before writing and again in the second pass:
empty Y is allowed and every H_v is empty; zero-dimensional V means empty I, whose
zero family can generate an invertible sheaf only on empty Y, so its affine coefficient
space is Spec k and the conclusion still holds. For Y = Spec k and one generating
section, nonzero coefficients have empty zero scheme and coefficient zero has Y,
both smooth. For P^1 with O(1), nonzero coefficients give smooth degree-one sections;
the bad zero tuple may be removed by U. For Y positive dimensional, the universal projection need not be smooth above the
zero tuple even though H_0 = Y is smooth, since flatness can fail there; the conclusion
concerns the zero scheme and never requires zero to lie in U. Finite fields require no
k-point in a nonempty open, and the statement instead quantifies over all extensions.
Positive/imperfect characteristics are all included. No effective-Cartier or nonempty
member assumption is added; H_v may be empty.

Searches made for an exact statement (2026-10-17 UTC):

- msearch.py leanfinder: "For a smooth scheme a general member of an immersive generated
  linear system is smooth"; 8 hits, smoothness definitions/open-immersion instances,
  no Bertini theorem.
- msearch.py leansearch: "general hyperplane section of a smooth scheme is smooth";
  8 hits, smoothness definitions/local criteria and one manifold sheaf result; no match.
- msearch.py loogle: "AlgebraicGeometry.Smooth, AlgebraicGeometry.IsImmersion"; 0 hits.
- msearch.py grep: `Bertini|bertini|smooth.*section`, AlgebraicGeometry; 0 hits in Mathlib.
- rg in upstream WeilConjectures and side lean/Sheaf for Bertini, smooth member,
  generating sections, zeroLocus and projective section constructors: upstream Bertini
  states only a special curve-through-points theorem, not this node. Read the entire
  upstream `AlgebraicGeometry/Bertini.lean`; no exact declaration. Found and reused the
  section/projective/zero-scheme interfaces above.
- grep -rn for the exact node id in upstream, and rg of the exact id/new theorem/helper
  names in upstream, side Lean, and dag/lean_names_upstream.json: no existing statement
  or collision. No notion was redefined instead of using its recorded declaration.

Validation: scompile.py compiles the sandbox and its actual library module independently
under the default 60-second limit, both clean (4.2 s and 4.3 s). autoImplicit is explicitly
false. Definitions have real terms and the only postponed proof is the named main theorem.

## Second reading by Q107

I reopened the node statement and the complete final Lean module for a separate second
pass. This is the worker's second pass; the dispatcher prohibits starting another agent,
and the maintainer's independent review will read the delivery. I checked every clause
listed above directly in both files.

The first compile found that `L.sections` lacks the additive structure required by `→+`;
ψ now takes values in the top-open section module, and `bertiniSectionFamily` uses the
existing canonical conversion. I checked the scalar law uses f.appTop, not an arbitrary
k-action, and that generation and the projective map use the exact same ψ(b_i). I also
changed a natural-number coordinate label to an arbitrary finite `I : Type u`, avoiding
a hidden restriction from the projective constructor's index universe while retaining
all finite-dimensional spaces, including the empty basis. Finally I explicitly supplied
`k := k` at the coefficient point to ensure its polynomial coefficient ring is the base
field, not an unresolved choice. The sum's coefficients come from the second projection
and its sections from the first projection's tensor-pullback unit. The final smooth
morphism is H_v → Y_K → Spec K. The field quantifier is inside the single-open existential,
which preserves the uniform extension-field clause. No mathematical mismatch remains.
