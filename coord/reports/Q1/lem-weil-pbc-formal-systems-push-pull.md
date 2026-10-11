## Worker report

The module `Sheaf.AlgebraicGeometry.FormalSystemsPushPull` states
`AlgebraicGeometry.exists_formalSystemsPushPull`, with proof `sorry`. No definitions,
new nodes, dependency replacements, or statement corrections are needed.

Read the node, all five statement dependencies and their complete declaration signatures
and docstrings. The local Stacks TeX is absent, so checked the source online at
https://stacks.math.columbia.edu/tag/088B (Lemma 30.25.3). It agrees with the node; coherence
of the pushforward is its first proof sentence. The docstring follows all eleven node
proof steps. Remark 0888 is represented in the node by the formal-kernel interpretation;
we state that interpretation exactly, rather than substitute termwise kernels.

Hypotheses and objects, clause by clause:

- Noetherian Y: `{X Y : Scheme.{u}} [IsNoetherian Y]`. X is not separately assumed
  Noetherian: it follows from properness over Y. In particular no extra instance binder
  strengthens the statement.
- Quasi-coherent ideals J,K: `(J K : Y.IdealSheafData)`, the shared bundled ideal sheaves.
- Proper f: `(f : X ⟶ Y) [IsProper f]`. Mathlib properness includes separatedness,
  universal closedness, and local finite type, with quasi-compactness following from
  universal closedness, hence agrees with finite type in the node.
- V is the complement of V(K): `K.support.compl`; Mathlib's ideal support is the
  affine-local zero locus, not the support of K as a module.
- Isomorphism over V: `_hV : IsIso (pullback.snd f (Scheme.Opens.ι K.support.compl))`.
  This is the base change X ×_Y V -> V, canonically the stated inverse-image restriction.
- I is the extended ideal: `J.comap f`, not a separate arbitrary ideal.
- Formal system G: `(G : CoherentFormalModule Y J)`.
- Coherent F: `(F : CoherentModules X)`; `F.obj` is the actual module and `F.property`
  is the shared coherence predicate.
- The specified isomorphism beta: `_β : G.obj ⋙ Scheme.Modules.tensorPullback f ≅
  formalCompletionSystem (J.comap f) F.obj`. These are the actual pulled-back terms,
  pulled-back transition maps, and actual adic quotients. This ambient natural isomorphism
  is precisely an isomorphism in the full subcategory Coh(X,I), by full faithfulness of
  its inclusion and the object conditions in the pullback dependency. The properness
  hypothesis implies X Noetherian, so the dependency applies. Writing it in the ambient
  category avoids choosing the existential functor in that dependency; it changes no
  objects or maps and imposes no additional hypothesis.

Conclusions, clause by clause:

- Coherence of f_*F: `∃ h : RingedSpace.IsCoherent Y.toRingedSpace
  ((Scheme.Modules.pushforward f).obj F.obj), ...`.
- Alpha is a morphism of Coh(Y,J) to the completion of exactly that pushforward:
  `∃ α : G ⟶ (completion Y J).obj ⟨(Scheme.Modules.pushforward f).obj F.obj, h⟩, ...`.
  The existential proof h allows the coherent object to be bundled without assuming
  the first conclusion in advance. No let binder, hidden have, or arbitrary completion.
- Positive integer exponent: `∃ t : ℕ, ... 1 ≤ t ∧ ...`; natural numbers at least one
  encode exactly integers at least one.
- Kernel and cokernel in Coh(Y,J): `k : KernelFork α`, `c : CokernelCofork α`, with
  `Nonempty (IsLimit k)` and `Nonempty (IsColimit c)`. Their points are the actual
  universal kernel and cokernel objects in the full formal category. This is equivalent
  to choosing kernels via the abelian structure supplied by the recorded dependency,
  but does not require a file-local Abelian instance or a new definition.
- Every term of both objects is killed by the same K^t: the final two conjuncts quantify
  `n : ℕ` and assert `IsZero (Scheme.idealModuleProduct
  (Scheme.idealSheafPower K.toModulesι t).2 (k.pt.obj.obj (op n)))`, respectively `c.pt`.
  Here op n is positive level n+1. Ideal-power annihilation uses the existing product
  and power, never an arbitrary morphism or a pointwise-kernel surrogate.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`;
  read also `IsSeparated` and `UniversallyClosed` in their defining modules.
- `Sheaf.AlgebraicGeometry.CoherentFormalModule`: `CoherentFormalModule`,
  `CoherentModules`, `formalCompletionSystem`, `completion`; the definitions use
  `IsCoherentFormalModule`, actual cokernel quotients, and shared ideal products/powers.
- `Sheaf.AlgebraicGeometry.Coherent`: `RingedSpace.IsCoherent`.
- `Sheaf.AlgebraicGeometry.FormalSystemsPullback`: `exists_formalSystemsPullback`;
  its recorded equation specifies the same ambient termwise tensor pullback used here.
  `Scheme.Modules.tensorPullback` is from its import
  `Sheaf.AlgebraicGeometry.TensorPullback`, whose definition was read.
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesAbelian`: `coherentFormalModule_abelian`;
  its abelian category is the category in which the universal forks/coforks are stated.
- Mathlib `Scheme.Modules.pushforward` (Modules/Sheaf.lean),
  `Scheme.IdealSheafData.comap` (IdealSheaf/Functorial.lean), and
  `Scheme.IdealSheafData.support` (IdealSheaf/Basic.lean), signatures/docstrings read.

Edge cases checked before writing: empty X/Y, zero F or G, J=0 (constant completion),
J=unit (zero formal system), K=0 (V empty; annihilation by K holds automatically),
K=unit (V=Y, so proper f is an isomorphism and the comparison must be an isomorphism).
No reducedness, separatedness of Y, characteristic, nonemptiness, or affine hypothesis
was added. A single shared scheme universe matches the existing category definitions;
no independent test-object universe makes a hypothesis vacuous. n=0 indexes level 1,
not an extra quotient by the zeroth power. Kernel and cokernel need not be termwise
kernels, and the universal-property encoding preserves this distinction.

Searches for an existing statement:

- `msearch.py ... leanfinder "coherent formal inverse systems proper pushforward
  pullback isomorphism kernel cokernel annihilated ideal power"`: eight hits on abstract
  inverse-system equivalences and adic completion transitions; none is this statement.
- `msearch.py ... loogle "AlgebraicGeometry.IsProper, CategoryTheory.Limits.KernelFork"`:
  zero hits.
- `msearch.py ... grep "formal.*push|formal.*pull|FormalSystem" AlgebraicGeometry`:
  one unrelated FormallyUnramified hit, no formal coherent-system comparison.
- `rg -n "lem-weil-pbc-formal-systems-push-pull|formalSystemsPushPull|formal.*push|formal.*pull"`
  in upstream `WeilConjectures`: only unrelated formalism/étale descent hits.
- `grep -rn "lem-weil-pbc-formal-systems-push-pull"` in upstream: no hits.
- `rg -n "FormalSystemsPushPull|exists_formalSystemsPushPull|formal.*push.*pull|formal.*pushforward"`
  in the project's `lean/Sheaf` and upstream: only citations of this node and the
  distinct closed-immersion pushforward statements, not this statement. The declaration
  name has no existing match.

The server compile is the validation gate; expected sorry is the only postponed proof.
No STATEMENT-DISPUTED issue found. The first compile exposed an elaboration issue in
field notation for a topological open; repaired with explicit `Scheme.Opens.ι`.

## Second reading by Q1

Independent second reader: opened the delivered node and module, all five dependency
nodes and their recorded declarations (including the full pullback and abelian theorem
signatures), and the underlying coherent-module, ideal, product, power, completion,
tensor-pullback and pushforward definitions. No mathematical mismatch found; the Lean
module and node record are unchanged. No new nodes, dependency modules or statement
correction are present, so H12/H13 and corrected-statement citer review do not apply.

Source read independently: downloaded the Stacks `coherent.tex` into the item's
`scratchpad/coherent.tex` from the official stacks/stacks-project repository. Read
Section `section-coherent-formal` (lines 6247 onward), Section
`section-existence-proper` (6876 onward), Remark
`remark-inverse-systems-kernel-cokernel-annihilated-by` (6887 onward) and Lemma
`lemma-inverse-systems-push-pull` with its full proof (7025 onward). Also opened tags
088B, 0888 and 0EHN online. There is no section-wide completeness, affine, field,
separated-base or characteristic hypothesis: completion and affineness are reductions
inside the proof. The explicit pushforward-coherence conclusion is justified by its
first sentence. The node agrees with this source.

Object/hypothesis/conclusion checklist (every verdict: exact):

- Schemes X,Y, with Y Noetherian: `{X Y : Scheme.{u}} [IsNoetherian Y]`.
  Mathlib `IsNoetherian` is locally Noetherian plus compactness. No separate assumption
  on X is added; proper finite type over Y implies X Noetherian.
- Quasi-coherent ideals J,K of O_Y: `(J K : Y.IdealSheafData)`; this is the shared
  affine-local ideal-sheaf encoding. `toModulesι` is its actual module inclusion.
- Proper f:X -> Y: `(f : X ⟶ Y) [IsProper f]`. Opened the Mathlib class and the
  `UniversallyClosed` quasi-compactness instance: locally finite type here is finite type.
- V=Y minus V(K): `K.support.compl`. Opened `supportSet_inter` and `support`:
  support is the zero locus of the ideal, not the nonzero-stalk support of its module.
- f is an isomorphism over V: `_hV : IsIso (pullback.snd f
  (Scheme.Opens.ι K.support.compl))`. This is exactly the base-changed map to V,
  isomorphic to f restricted to its inverse image. This hypothesis is not automatic.
- I=f^{-1}J O_X: `J.comap f`. Its definition is the ideal of the pulled-back closed
  subscheme, so it is the extended ideal, with no independent I or extra hypothesis.
- G in Coh(Y,J): `(G : CoherentFormalModule Y J)`. Opened
  `IsCoherentFormalModule`: coherent terms, J^(n+1) annihilation and precisely the
  quotient isomorphism induced by the transition map. Morphisms are compatible families.
- Coherent F on X: `(F : CoherentModules X)`, whose property is the recorded
  `RingedSpace.IsCoherent`. Opened that definition: finite type and finite-type kernels
  of every finite free map on every open; no replacement by finite presentation.
- Specified beta is an isomorphism f*G -> F-completion: `_β : G.obj ⋙
  Scheme.Modules.tensorPullback f ≅ formalCompletionSystem (J.comap f) F.obj`.
  The pullback dependency specifies exactly this composition on objects and maps.
  Its source-Noetherian hypothesis follows from properness. Both systems belong to
  Coh(X,I), and its full-subcategory inclusion is fully faithful; ambient isomorphisms
  and formal-category isomorphisms are the same data, with the same direction.
- f_*F coherent: `∃ h : RingedSpace.IsCoherent Y.toRingedSpace
  ((Scheme.Modules.pushforward f).obj F.obj), ...`. Opened pushforward: it is the
  actual sheaf-of-modules pushforward with sections over f-inverse images.
- A map alpha:G -> completion(f_*F) in Coh(Y,J): `∃ α : G ⟶
  (completion Y J).obj ⟨(Scheme.Modules.pushforward f).obj F.obj, h⟩, ...`.
  The completion is the recorded functor of actual cokernel quotients. The proof h
  merely bundles the preceding conclusion; it is not an additional hypothesis.
- One integer t>=1: `∃ (t : ℕ) ... 1 ≤ t ∧ ...`. Positive natural numbers cover
  exactly the allowed integers, and the same t occurs in both final clauses.
- Kernel and cokernel in the abelian formal category: `k : KernelFork α`,
  `c : CokernelCofork α`, `Nonempty (IsLimit k)`, `Nonempty (IsColimit c)`.
  These universal properties determine the actual formal kernel/cokernel up to
  isomorphism, independently of a chosen Abelian structure. The recorded abelian
  theorem applies without any added instance. Fork points are objects of Coh(Y,J),
  not ambient termwise kernel systems.
- Every term of both objects killed by K^t: the final two `∀ n : ℕ, IsZero
  (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
  (k.pt.obj.obj (op n)))` / corresponding `c.pt` clauses. Opened product and power:
  they are the image of multiplication and iterated ideal products. IsZero means
  that product sheaf is zero. On affines the formal kernel terms are Ker(alpha_U)
  modulo J^n; formal cokernels are Coker(alpha_U) modulo J^n. Uniform annihilation
  of these is equivalent to annihilation of the finite complete kernel/cokernel
  modules. Remark 0888 then identifies this existence assertion with its uniform
  termwise-kernel formulation. The exponent can double in that equivalence, but no
  exponent is prescribed here, so the node's explicit formal-kernel reading and
  the source have the same strength. Nothing asserts equality of termwise kernels.

Edge cases: empty Y forces empty X and gives zero sheaves, so the conclusion includes
that case; no nonempty binder occurs. Empty X over nonempty Y remains allowed whenever
the stated isomorphism-over-V hypothesis holds. Zero G/F, J=0 (constant adic systems),
J=unit (zero systems), K=0 (V empty, annihilation automatic) and K=unit (V=Y,
f an isomorphism and the comparison an isomorphism) are covered. `op 0` means level 1;
no quotient by the zeroth power is imposed. No arbitrary index-set nonemptiness is
assumed: the source's indexing is the positive integers. No characteristic restriction
is introduced. `u` is arbitrary, and schemes and their module categories use the shared
recorded universe convention, with no quantification over a too-small test universe.

Independent searches using different queries from the first reader:

- LeanSearch via msearch: "A coherent formal system whose pullback along a proper
  scheme morphism is a completion maps to the completed pushforward with kernel and
  cokernel killed by an ideal power": service unavailable (Internal Server Error);
  recorded as unavailable, not evidence of absence.
- LeanFinder via msearch: "proper morphism coherent adic systems exceptional locus
  comparison completion": eight hits, including `AdicCompletion.map_exact` and
  affine-transition-limit results. These concern ring-module completion or limits of
  schemes, not this formal-system push-pull comparison.
- Loogle via msearch: `AlgebraicGeometry.IsProper,
  CategoryTheory.Limits.CokernelCofork`: zero hits. An earlier query using
  `AlgebraicGeometry.CoherentFormalModule` reported an unknown identifier, so was
  not used as absence evidence.
- Grep via msearch: `inverse.*system|formal.*module` in AlgebraicGeometry: three
  hits, all inverse systems of qcqs schemes in AffineTransitionLimit, not this result.
- Independent `rg -n -i` in Mathlib, upstream WeilConjectures and project lean/Sheaf
  for `formalSystemsPushPull|inverse.systems.push.pull|formal.{0,25}(pushforward|push.pull)|
  adic.{0,25}(pushforward|comparison)`: no declaration of the item; project hits are
  citations in the two Grothendieck-existence modules, upstream hits are unrelated
  pro-etale adic comparisons. No duplicate notion or theorem warrants `existing: true`.

H5/H6/H8/H9 checked: the delivery declares just one theorem, with proof `sorry`, and
no definitions or local instances/notations. Module and declaration docstrings give
088B/0888 and the exact blueprint id. The eleven numbered docstring steps match the
node's eleven proof steps: setting, coherence, gamma/kappa, affine construction, gluing,
completion base change, invariance, algebraization, the adjunction map, support, and
uniform annihilation. Names, imports, bound universe/variables and line widths comply.
The node's `lean.statement` was checked against the exact multiline signature up to
`:= by` and is verbatim equal. Server scompile completed cleanly in 1.9 seconds, exit 0,
with no errors or warnings. Second reading changes only this review report; no repairs
were needed to the statement or source module.
