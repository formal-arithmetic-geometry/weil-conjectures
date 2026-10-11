## Worker report

The module states algebraization by devissage for a coherent formal module `M` on a
Noetherian scheme `X`. The ideals `I` and `K` are `Scheme.IdealSheafData`; the thickening
at level `e` is `(K ^ e).subscheme` with immersion `(K ^ e).subschemeι`, and the induced
ideal is `I.comap ...`. Hypothesis `hthick` renders equivalence of the completion functor
on every thickening (an explicit `IsNoetherian` witness is quantified because Mathlib does
not synthesize noetherianity of the subscheme). `H` is the coherent module used for the
comparison completion and `α` is its formal-module morphism. `htorsion` gives a positive
power `t`, kernel and cokernel forks with limit/colimit witnesses, and annihilation of all
components by `K^t`. The conclusion is a coherent module `F` and an isomorphism from its
completion to `M`.

Dependency declarations used: `Sheaf.AlgebraicGeometry.CoherentFormalModule` (`CoherentFormalModule`, `completion`); `Sheaf.AlgebraicGeometry.CoherentFormalModulesAbelian` (`coherentFormalModule_abelian` provides the abelian kernel/cokernel setting); `Sheaf.AlgebraicGeometry.CoherentFormalModuleAnnihilated` (`AnnihilatedBy` and the kernel/cokernel annihilation formulation); Mathlib `AlgebraicGeometry.Scheme.IdealSheafData.subscheme`, `subschemeι`, `comap`, and `IsNoetherian`.

Edge cases checked: positive indices are enforced by `1 ≤ e` and `1 ≤ t`; the formal-system index is `ℕᵒᵖ` with all levels quantified; zero kernel/cokernel are allowed through `IsZero`; no nonemptiness assumption on the scheme is introduced.

Searches: `msearch.py leanfinder` (Grothendieck existence for formal coherent modules; no match), `msearch.py loogle` (completion/equivalence names; only ring-level adic completion), grep of Mathlib AlgebraicGeometry/RingTheory (no sheaf existence theorem), `rg` in WeilConjectures and `lean/Sheaf` (no prior declaration of this lemma). The file compiled cleanly with `scompile.py`.

## Earlier second reading (a previous round; superseded)

The statement and file were read against every clause of the node. `X`, `I`, `K`, and `M` match the node; `hthick` gives the completion equivalence for each `K^e` thickening; `α` and `htorsion` render the comparison and uniform kernel/cokernel annihilation; the existential conclusion is the essential-image assertion. The explicit noetherian witness is required only to apply the existing `completion` definition.


## Second reading by Q1

Read the node, its nine statement dependencies and their recorded declarations, the
module, Stacks coherent.tex Lemma 088A (lemma-existence-tricky), its entire proof,
and the surrounding Section 0886 and Remark 0888. The local Stacks source is available
in c1-stacks-review/coherent.tex; the repository literature checkout is absent.
The source agrees with the node. There is no statement_change, new definition node,
or dependency module in this delivery.

Object/hypothesis/conclusion checklist (the node statement decomposed before comparison):

1. A Noetherian scheme X: `{X : Scheme.{u}} [IsNoetherian X]`. PASS.
   Mathlib Noetherian.lean defines this as locally Noetherian plus CompactSpace,
   exactly the node's locally Noetherian and quasi-compact underlying space.
2. Quasi-coherent ideals I and K in O_X: `(I K : X.IdealSheafData)`. PASS.
   This is the shared affine-ideal encoding, with the recorded `toModulesι`
   inclusions; no abstract mono or private notion is introduced.
3. For every positive e, X_e = V(K^e), with its closed immersion i_e:
   `(K ^ e).subscheme` and `(K ^ e).subschemeι` in `hthick`, guarded by
   `1 ≤ e`. PASS. Read Mathlib Subscheme.lean's construction and the recorded
   closed immersion/ideal kernel declarations: this is the closed subscheme,
   not merely its reduced support. IdealSheafData powers are actual ideal powers.
4. I_e = I O_{X_e}, the image of the pulled-back ideal:
   `I.comap (K ^ e).subschemeι`. PASS. Read Mathlib Functorial.lean:
   `comap` is the kernel ideal of the base-changed closed immersion, which is
   the extended ideal, and `comapIso` identifies its subscheme with that pullback.
5. A formal coherent object (F_n): `(M : CoherentFormalModule X I)`. PASS.
   Opened CoherentFormalModule.lean: its full-subcategory predicate requires
   coherence, I^(n+1) annihilation, and the quotient-induced transition iso.
   Morphisms are compatible natural transformations. `op n` is positive level n+1.
6. Completion is an equivalence on each X_e:
   `hthick : ∀ e, 1 ≤ e → ∀ hZ : IsNoetherian (K ^ e).subscheme,
   Functor.IsEquivalence (@completion ... hZ (I.comap ...))`. PASS.
   The completion definition is the actual quotient system G/I_e^(n+1)G,
   not a constant system. The quantified hZ is a proof witness, not an extra
   restriction: closed immersions are locally of finite type, so Mathlib's
   LocallyOfFiniteType.isLocallyNoetherian supplies local noetherianity;
   the closed immersion is quasi-compact and its source is compact over compact X.
   Hence the hZ type is inhabited for every e. Proof irrelevance makes the choice
   immaterial. No independent test-scheme universe makes this hypothesis vacuous.
7. A coherent H and a map alpha : M → H^:
   `(H : CoherentModules X)` and `(α : M ⟶ completion X I |>.obj H)`. PASS.
   Read CoherentModules and RingedSpace.IsCoherent in Coherent.lean: the full
   subcategory uses finite type and finite-type kernels of maps from finite free
   modules on every open. Supplying any witnesses H and alpha as theorem arguments
   renders the node's existential hypothesis without asserting they always exist.
8. A uniform positive t with kernel and cokernel in Coh(X,I) killed by K^t:
   `htorsion : ∃ t, 1 ≤ t ∧ ∃ k : KernelFork α, ∃ c : CokernelCofork α,
   Nonempty (IsLimit k) ∧ Nonempty (IsColimit c) ∧ ...` followed by zero ideal
   products on `k.pt.obj.obj (op n)` and `c.pt.obj.obj (op n)` for every n. PASS
   AFTER REPAIR. The previous forks were of `α.hom`, so their objects and
   universal properties lived in all inverse systems, not Coh(X,I).
   Replaced α.hom by α and added the second `.obj` when evaluating fork points.
   This now matches exactly condition (4) of the recorded
   coherentFormalModule_annihilated_iff. Read coherentFormalModule_abelian:
   it asserts existence of an abelian structure and termwise cokernels;
   formal kernels need not be the termwise kernels. Universal forks express the
   intrinsic kernel/cokernel without adding an Abelian instance hypothesis.
   Both ideal products use the shared idealSheafPower/idealModuleProduct definitions.
9. Essential-image conclusion: `∃ F : CoherentModules X,
   Nonempty ((completion X I).obj F ≅ M)`. PASS. This asserts the coherent
   algebraization and an iso of formal systems, with no additional compatibility,
   uniqueness, or proper-support condition absent from the node.

Edge cases: empty X is allowed (no Nonempty or point binder); zero modules and zero
kernel/cokernel are allowed (IsZero is the correct module-category zero condition).
Zero and unit ideals, nonreduced schemes, and every characteristic are allowed.
The formal index is the fixed nonempty positive-integer system, with Lean n=0
representing Stacks level 1, so no unwanted level-zero condition is imposed.
e=0 and t=0 are deliberately excluded exactly as the source excludes them.
The single arbitrary universe u agrees with the shared Scheme.{u}/X.Modules
encoding and imposes no finite cardinality bound or independent smaller test universe.

Independent searches, using wording different from the worker's searches:
- msearch leanfinder: "algebraization of coherent adic sheaves from torsion comparison
  and closed infinitesimal neighborhoods". Eight hits: localCohomology,
  AdicCompletion.flat_of_isNoetherian, formal smooth/unramified ring results,
  and an affine-limit section lemma. None states this sheaf algebraization lemma.
- msearch loogle: "Functor.IsEquivalence, AlgebraicGeometry.Scheme" returned no hits,
  with an unknown-identifier diagnostic; this is not evidence of absence.
- msearch leansearch: full description of completion equivalence on ideal-power
  subschemes plus a torsion comparison. Service unavailable (Internal Server Error);
  no mathematical verdict inferred from that unavailable search.
- rg in all Mathlib, WeilConjectures and lean/Sheaf for existence_devissage,
  existence-tricky, 088A, and algebraization/formal combinations, and in the upstream
  name table. No existing declaration of this statement. Read neighboring project
  GrothendieckExistence/Proper/Projective signatures: these assume a complete Noetherian base ring and concern proper support,
  proper morphisms, or projective embeddings, respectively; they are different theorems. Shared notions already
  exist in the dependency modules and were retained.

Other mismatches repaired: the original two-sentence proof docstring omitted most of
steps 2, 3, 4 and 5 and their named dependencies. Replaced it by all five node steps,
including quotient systems, the 2t/4t bounds, easy algebraization and levelwise
uniqueness. Added the standard copyright/license header. Removed the unused direct
CoherentFormalModuleAnnihilated import; retained CoherentFormalModule and
CoherentFormalModulesAbelian for the formal category and its preadditive structure.
There are no definitions, no private copies, no proofs beyond the single named
`sorry`, no file-local notation/instances, no statement-level lets, no unbound
variables or universes, and all lines have at most 100 characters. Updated
lean.statement verbatim to the repaired theorem signature. The mathematical node
statement, its dependencies and its proof were left intact.

Validation: scompile.py compiled the repaired single module cleanly in 1.8 seconds,
with no errors or warnings. The server compile uses the project tool, never a global
library build. Delivery dry run and final delivery are performed after this reading.
