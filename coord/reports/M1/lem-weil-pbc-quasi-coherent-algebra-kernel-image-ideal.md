## Worker report

The module `Sheaf.AlgebraicGeometry.QuasiCoherentAlgebraKernelImageIdeal` states the two parts
of the node as `AlgebraicGeometry.Scheme.CommAlgebraSheaf.kernel_image_quasiCoherent` and
`AlgebraicGeometry.Scheme.CommAlgebraSheaf.generated_ideal_quotient_quasiCoherent`. Both
proofs are `sorry`; there are no definitions or further postponed proofs. The existing
algebra-sheaf node `def-weil-pbc-comm-algebra-sheaf` is added to statement dependencies.
There is no statement correction and no disputed statement.

Hypotheses and clauses, in the order of the node:

- The scheme is `{X : Scheme.{u}}`, with no Noetherian, quasi-compact, quasi-separated or
  nonempty hypothesis. Algebra sheaves are the existing `X.CommAlgebraSheaf = Under X.sheaf`.
  Their commutative rings, structure maps and morphisms commuting with those structure maps
  come from that category. Quasi-coherence means `B.toModule.IsQuasicoherent`, exactly the
  quasi-coherence of the underlying module (not any finiteness property).
- Part (a): `B A`, `hB hA`, and `ψ : B ⟶ A` give precisely the two quasi-coherent algebras
  and the algebra map. The existential `J : X.Modules`, `i : J ⟶ B.toModule`, together with
  injectivity of `i.app U` on every open, realizes a module subsheaf of B. Its section range
  equals `RingHom.ker (ψ.right.hom.app (op U)).hom` on EVERY open U, so it is a sheaf of ideals
  and the kernel sheaf. `J.IsQuasicoherent` supplies quasi-coherence. The affine kernel formula
  follows immediately from the asserted formula for all opens, as specified by the node.
- The existential algebra `D`, its algebra inclusion `k : D ⟶ A`, and injectivity on EVERY
  open realize the subalgebra sheaf of A. `D.toModule.IsQuasicoherent` supplies quasi-coherence.
  For every section s over U, membership in its section range is equivalent to every point
  x of U having an open V ≤ U containing x whose restricted section is in the range of ψ_V.
  This is exactly the node's local-image definition (including restrictions via hVU).
  The final affine-open clause equates the two section ranges, giving Im(ψ)(U) = ψ_U(B(U)).
- Part (b): `B`, `hB`, `E : X.Modules`, `hE` and `e : E ⟶ B.toModule` introduce precisely
  the quasi-coherent algebra, quasi-coherent module and linear sheaf map in the node.
- `J`, `i`, `I : ∀ U, Ideal (B.right.obj.obj (op U))` give the generated ideal sheaf:
  injective i_U and `range i_U = I U` identify each section ideal with the module subsheaf.
  `J.IsQuasicoherent` is its quasi-coherence; `range e_U ⊆ I U` is containment on EVERY open.
  Minimality quantifies over every module sheaf K with a sectionwise injective inclusion j
  and section ideals L equal to its ranges. Containment of each e_U then implies `I U ≤ L U`
  for every open. Thus this is the smallest sheaf of ideals in exactly the sense of the node;
  the competing ideal sheaf is NOT required to be quasi-coherent.
- On every affine U, `I U = Ideal.span (Set.range (e.app U))` is the generated-section-ideal
  formula. The set type annotation fixes B(U)'s ring structure rather than the bare
  additive-module section carrier.
- The μ clause takes the source to be the sheafification of the existing presheaf tensor
  `PresheafOfModules.Monoidal.tensorObj (R := X.sheaf.obj) B.toModule.val E.val`. It is the
  tensor product of the dependency node's definition, stated in the literal sheafification
  form rather than choosing a second monoidal instance. The existing module sheafification
  adjunction unit is used to send b ⊗ s to that sheaf's sections, and μ sends it to b e_U(s).
  Multiplication is explicitly `@Mul.mul (B.right.obj.obj (op U)) inferInstance` because
  the same section carrier also has a bare module-category presentation without a ring
  instance. The following local-preimage equivalence identifies I with the sheaf image of μ
  on ALL opens, exactly the tensor-image clause.
- `Q : X.CommAlgebraSheaf`, `q : B ⟶ Q`, `P` and `p : B.right.obj ⟶ P` supply the quotient.
  Each p_U is a SURJECTIVE ring map with kernel I U. This specifies the section quotient
  ring B(U)/I(U) up to its canonical isomorphism, with the quotient restrictions determined
  by p's naturality and surjectivity. The explicit isomorphism
  `a : (presheafToSheaf ... CommRingCat).obj P ≅ Q.right`, and equality
  `q.right.hom = p ≫ sheafificationAdjunction.unit.app P ≫ a.hom.hom`, specify Q as its
  SHEAFIFICATION WITH THE QUOTIENT MAP, not an unrelated abstract algebra.
- `Q.toModule.IsQuasicoherent` is quotient quasi-coherence. The local-preimage condition
  for q on every section/open/point is surjectivity of the sheaf map; it does not incorrectly
  demand surjectivity on every non-affine open. On affine opens the next clause explicitly
  demands sectionwise surjectivity and kernel I U, hence the stated affine quotient formula.
- The final clause quantifies over EVERY algebra sheaf C (without quasi-coherence assumed)
  and χ : B ⟶ C. The all-section condition `χ_U(e_U(s)) = 0` is χ ∘ e = 0. Its conclusion
  `∃! χbar : Q ⟶ C, q ≫ χbar = χ` is precisely the algebra-map factorization and uniqueness.

Dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations `AlgebraicGeometry.Scheme`
  and `Scheme.Hom` (locally affine locally ringed spaces and their morphisms).
- `def-weil-sheaf-of-modules-category`: Mathlib `SheafOfModules` and its `Hom`; schemes use
  `Scheme.Modules` (definitionally these module sheaves), `Scheme.Modules.Hom.app`, and the
  presheaf morphism application `μ.val.app`. The abelian-category assertions are not added
  as independent hypotheses; the scheme instances are already available.
- `pqf-def-coherent`: `Sheaf.AlgebraicGeometry.Coherent`, read `RingedSpace.IsCoherent` and its
  module docstring specifying quasi-coherence as the existing `SheafOfModules.IsQuasicoherent`.
  Read that predicate's full signature and docstring in Mathlib's Sheaf/Quasicoherent.lean.
  This node uses only its quasi-coherent clause, so it does not impose coherence.
- `def-weil-pbc-sheafification`: `Mathlib.CategoryTheory.Sites.Sheafification`,
  `CategoryTheory.presheafToSheaf` and `CategoryTheory.sheafificationAdjunction`.
- `def-pur-sheaf-tensor-product`: read the whole shared tensor module
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct` and the source's
  `SheafOfModules.tensorObjIsoSheafification`, which states the identification of its tensor
  with the sheafification used here. Read Mathlib `PresheafOfModules.Monoidal.tensorObj` and
  its full section/restriction definitions. No duplicate tensor notion is introduced.
- Added landed dependency `def-weil-pbc-comm-algebra-sheaf`:
  `Sheaf.AlgebraicGeometry.CommAlgebraSheaf`, `Scheme.CommAlgebraSheaf` and `.toModule`, read
  with their signatures and docstrings. No private algebra-sheaf definition is introduced.

Sources checked: local Stacks .tex files are not present in this clone; opened the actual
Stacks pages instead: https://stacks.math.columbia.edu/tag/01LA (items (1),(5),(8)),
https://stacks.math.columbia.edu/tag/05JS (kernel, generated ideal, quotient in the proof),
and https://stacks.math.columbia.edu/tag/0817 (same constructions used in (2)). The module's
proof docstrings carry the node's steps 0–6 and name the corresponding proof nodes. Its
statements add none of the qcqs hypotheses of the enclosing 05JS/0817 approximation results:
the kernel/image/tensor/quotient permanence facts are local and hold on any scheme (01LA).

Edge cases checked mathematically before writing:

- Empty scheme and empty open: the kernel/ideal section formulas and local-preimage
  conditions agree with the unique zero-ring/module sections; no Nonempty binder excludes them.
- Zero algebra sheaf, zero module E and zero e: the generated ideal is zero, μ is zero,
  and the quotient is B. A zero target algebra in (a) has full kernel and zero image.
- Identity ψ: zero kernel, full image. Units and structure-ring sections are present because
  k is an algebra morphism; the image is not merely an additive submodule.
- e containing the unit: the generated ideal is the whole algebra and the quotient is the
  zero ring, which is permitted. The universal property then requires χ to kill the unit.
- No affine-open choice, finite rank, field characteristic or independent test universe
  is imposed. All sheaf objects use the shared scheme/module universe u.
- Non-affine opens need not have surjective section quotient maps; only local surjectivity
  is asserted there. The affine clauses give the stronger correct sectionwise statements.

Searches for reuse (all on 2026-10-11, using msearch.py with group/item as in the brief):

- LeanFinder: "Kernels images and quotients of quasi-coherent sheaves of commutative algebras
  on a scheme and generated ideal affine sections". Eight hits, including
  `Scheme.Hom.ker_apply`, `Scheme.ker_morphismRestrict_ideal`, `Scheme.ker_of_isAffine`, and
  `Scheme.IdealSheafData` lemmas. These concern ideals of the structure sheaf and kernels of
  scheme morphisms, not ideals in an arbitrary algebra sheaf. No exact match.
- Loogle: "SheafOfModules, Algebra, Sheaf, CommRingCat". No hits; service reported unknown
  identifier Sheaf. Followed with the valid query "RingHom.ker, Ideal.span", yielding twelve
  ring-level kernel/span facts (polynomial evaluation, localizations, idempotents), no
  sheaf-algebra permanence statement.
- LeanSearch: "ideal subsheaf of a sheaf of commutative algebras on a scheme". UNAVAILABLE:
  service returned Internal Server Error. Recorded as unavailable, with no verdict;
  continued with LeanFinder, Loogle and source grep as instructed by the search tool.
- msearch grep: "CommAlgebraSheaf|AlgebraIdealSheaf|IdealSubsheaf|IsIdealSubmodule",
  Mathlib/AlgebraicGeometry: zero hits. Follow-up grep
  "kernel.*IsQuasicoherent|image.*IsQuasicoherent|quotient.*IsQuasicoherent" in that directory:
  zero hits. This agrees with the stage-1 search record in the node.
- rg on WeilConjectures and Mathlib for `CommAlgebraSheaf`, both new theorem names, and on
  `dag/lean_names_upstream.json`: no matches. rg for the item id in WeilConjectures: no hits.
  `tools/lean_names_upstream.py show <item>` gave only the index summary, no mapped declaration.
- rg on lean/Sheaf found the landed CommAlgebraSheaf and QuasiCoherentAlgebra modules, whose
  full definitions were read and reused. Searching the two new theorem names there gave no
  collision. The statement's notions are all expressed with existing module sheaves, ideals,
  morphisms, section ranges, presheaf tensor and sheafification; no new definition node is needed.
- `tools/blueprint_refs.py search 'ideal sheaf'` found thirteen blueprint nodes about
  structure-sheaf ideals, divisors and closed subschemes; `rg` in DAG nodes for ideals in
  algebras found this node and its approximation citer. No existing exact theorem was found.

Validation: server scompile accepted both statements with no errors or warnings. Compiler
feedback required specifying the ring section carrier for Ideal.span and multiplication,
and using μ.val.app for the sheafified tensor map (it is a SheafOfModules morphism rather
than a Scheme.Modules wrapper). These are elaboration fixes, not statement changes.

## Second reading by M1

I independently opened the sandbox node and both theorem signatures, all six statement
 dependency nodes and their recorded source declarations, and the Stacks source places.
There is no `statement_change`, new definition node, or dependency module in this delivery.
The added CommAlgebraSheaf dependency is already landed, not a new definition.

Objects, hypotheses and conclusions checked against the node, clause by clause:

1. An arbitrary scheme X: `{X : Scheme.{u}}` in both declarations. Mathlib's Scheme
   extends LocallyRingedSpace with local affine charts. No qcqs, Noetherian, separated,
   nonempty, finite-dimensional or characteristic assumption is imposed. PASS.
2. Commutative O_X-algebras and their underlying modules: `X.CommAlgebraSheaf` is the
   landed `Under X.sheaf`; its maps commute with O_X structure maps. The landed `toModule`
   restricts scalars on the algebra's rank-one module along that structure map. Its
   section carrier is the algebra section ring. `X.Modules` is the existing category of
   module sheaves and `i.app`, `e.app` are its linear section maps. PASS.
3. Quasi-coherence: `hB`, `hA`, `hE` assert precisely `IsQuasicoherent` of the underlying
   modules. Opened Coherent.lean and Mathlib's IsQuasicoherent/QuasicoherentData: this is
   local presentation by free modules, equivalent on schemes to the node's affine-local
   tilde-module condition. No finite type or coherent assumption is substituted. PASS.
4. Part (a) inputs: `(B A : X.CommAlgebraSheaf)`, their two quasi-coherence hypotheses,
   and `(ψ : B ⟶ A)` give exactly the stated algebra morphism. PASS.
5. Kernel ideal sheaf: existential `J`, `i` with injective `i.app U` and range equal to
   `RingHom.ker (ψ.right.hom.app (op U)).hom` for every open U. Naturality of i makes the
   ideals a subsheaf; `J.IsQuasicoherent` gives the required permanence. Its all-open
   equality includes the node's affine kernel equality without a stronger conclusion:
   the node itself defines the kernel sectionwise on all opens. PASS.
6. Image subalgebra: existential algebra `D` and algebra inclusion `k : D ⟶ A`, injective
   on every open, with quasi-coherent underlying module. The range equivalence says each
   point x of U has `V ≤ U` containing x whose restricted section lies in `range ψ_V`.
   This exactly specifies the locally defined image, including restriction to V. PASS.
7. Affine image formula: `IsAffineOpen U → range k_U = range ψ_U`. No global sectionwise
   image condition is imposed on non-affine opens. PASS.
8. Part (b) inputs: B and hB, E and hE, and linear map `e : E ⟶ B.toModule` are precisely
   the node's algebra, module, quasi-coherence hypotheses and linear map. PASS.
9. Generated ideal subsheaf: J and injective inclusion i realize each ideal `I U` as the
   section range, giving sheaf gluing and natural restriction; `J.IsQuasicoherent` is the
   desired property. `range e_U ⊆ I U` is required on every open. PASS.
10. Smallest ideal sheaf: the quantified competitors K, j and L require a sheaf inclusion
    whose section ranges are ideals and contain every `range e_U`; conclusion `I U ≤ L U`
    holds on all opens. No quasi-coherence restriction is placed on competitors. This
    covers every ideal subsheaf, rather than only quasi-coherent competitors. PASS.
11. Affine generated-ideal formula: `IsAffineOpen U → I U = Ideal.span (range e_U)` uses
    the ring carrier `B.right.obj.obj (op U)`. PASS.
12. Tensor multiplication and image: μ has source the sheafification of the shared
    `PresheafOfModules.Monoidal.tensorObj` of B and E. Opened the shared tensor module,
    upstream `tensorObjIsoSheafification`, presheaf tensor definition/restrictions, and
    module `sheafification`/`sheafificationAdjunction`. The source is exactly the tensor
    notion of def-pur-sheaf-tensor-product, without choosing a second tensor instance.
    μ after the adjunction unit sends each pure tensor to `b * e_U(s)`. The local-range
    equivalence for every U identifies I with its sheaf image. PASS.
13. Quotient construction: existential presheaf P and natural ring map p have surjective
    section maps with kernel I U on every open, specifying B(U)/I(U) and its induced
    restriction maps up to canonical isomorphism. The sheafification iso a identifies P's
    associated sheaf with Q, and the equation for `q.right.hom` ties q to p, the standard
    sheafification unit and a. Opened `presheafToSheaf` and `sheafificationAdjunction`.
    Q is a commutative O_X-algebra, not just a module quotient. PASS.
14. Quotient quasi-coherence and surjectivity: `Q.toModule.IsQuasicoherent`; each section
    of Q locally lies in the range of q. The latter is surjectivity as a sheaf morphism.
    On affine U, q_U is explicitly surjective with kernel I U, giving the stated quotient
    section ring. No false sectionwise surjectivity on general opens is added. PASS.
15. Quotient universal property: every algebra sheaf C and map χ killing `e_U(s)` for
    every open and section admits `∃! χbar : Q ⟶ C, q ≫ χbar = χ`. This is exactly χ ∘ e = 0
    and the unique factorization, with no quasi-coherence hypothesis on C. PASS.

Source verification: this clone lacks the Stacks .tex files. I fetched the actual
`schemes.tex` and `properties.tex` from the Stacks project's repository into this item's
scratchpad and read schemes.tex 1419–1431 and 4717–4752 and properties.tex 3320–3337,
3390–3418 and 3450–3488. Also opened Tags 01IC, 01LA, 05JS, 086N and 0817 on the Stacks site.
01LA's permanence list assumes only a scheme; the qcqs hypotheses in the Properties
approximation lemmas are needed for global approximation, not for these local
kernel/image/ideal/quotient constructions. The Lean and node correctly retain arbitrary X.
The two proof docstrings jointly carry steps 0–6 and their cited proof nodes, including
local image algebra closure, tensor multiplication, ideal minimality, quotient
sheafification/module-cokernel comparison and unique algebra factorization.

Edge cases: the empty scheme and empty opens are included (local-preimage clauses become
vacuous, as they should for the unique section). Zero E or e gives zero generated ideal
and quotient B; a zero target of ψ gives full kernel and zero image. Identity ψ gives zero
kernel and full image. If e contains 1, the generated ideal is full and the quotient is the
zero ring; CommRingCat admits it, and the universal property permits exactly the maps
killing 1. No index set or n is present; no finite generation or characteristic binder
exists. Universe u is arbitrary and shared by scheme, rings and module sheaves. Any family
of larger module carriers can be accommodated by increasing u; no independent smaller test
universe makes an assertion vacuous. General-open versus affine-open surjectivity was
checked separately. PASS.

Independent reuse searches (2026-10-11):

- LeanFinder through msearch: "quasicoherent algebra morphism image subsheaf generated ideal
  tensor multiplication quotient universal property". Eight hits, chiefly
  Scheme.IdealSheafData and QuasicoherentData generators. IdealSheafData concerns ideals of
  O_X, not an arbitrary algebra B; none states this node.
- Loogle through msearch: `SheafOfModules.IsQuasicoherent`. Twelve hits: the predicate,
  presentations, restriction and pushforward facts. No algebra kernel/image/generated
  ideal/quotient theorem. Opened the predicate and its local presentation data.
- LeanSearch through msearch: "image of multiplication from an algebra sheaf tensor a
  module generates an ideal sheaf". UNAVAILABLE (Internal Server Error); no verdict based
  on that service. LeanFinder, Loogle and source searches remain available.
- Independent rg in Mathlib's ModuleCat and AlgebraicGeometry, the full WeilConjectures
  source and lean/Sheaf for quasi-coherence with kernel/image/quotient, ideal subsheaf,
  algebra ideal sheaf and both delivered declaration names. Found upstream
  `Scheme.Modules.isQuasicoherent_kernel`; opened its signature: it only gives module
  kernel quasi-coherence, not this node's algebra image and generated-ideal/quotient
  clauses. The project's IdealTimesQuasiCoherentAffineSections concerns structure-sheaf
  ideals acting on a module, not arbitrary algebra ideals. No exact theorem or name
  collision was found. Existing algebra, module, tensor and sheafification notions are
  reused; no missing notion requires a new node or dependency module.

Mismatches and repairs: none in the node/Lean comparison; no Lean or node field was
rewritten. The second reading adds this independent report and reuse-search evidence.
There are two named theorem sorries, no definitions, no hidden data holes and no proved
statement. Both universe and all variables are explicitly bound. All lines fit 100
characters. Imports serve the existing algebra, quasi-coherence, tensor and ring-ideal
notions. The node's lean.statement is verbatim equal to the first theorem signature;
the declarations list also records the second theorem realizing part (b).

Validation: scompile on the absolute sandbox module path compiled the complete delivery
in 5.4 seconds, exit 0, with no errors or warnings. The initial relative-path invocation
could not locate the sandbox file; corrected the invocation to its absolute path, with
no change to the tool or module.
