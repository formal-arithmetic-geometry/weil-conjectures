## Worker report

The module `Sheaf.AlgebraicGeometry.ClosedImmersionUnitQuotient` states
`closedImmersion_unit_quotient`.  It uses the existing declaration
`AlgebraicGeometry.Scheme.Modules.tensorPullback` from
`Sheaf.AlgebraicGeometry.TensorPullback` (the recorded dependency
`def-pc-module-pullback`) and the existing adjunction construction
`AlgebraicGeometry.Scheme.Modules.exists_tensorPullbackAdjunction` from
`Sheaf.AlgebraicGeometry.TensorPullbackAdjunction`.

The hypotheses and clauses are rendered as follows.  The schemes are explicit
universe-`w` schemes `Y` and `Z`, and `i : Z ⟶ Y` is explicit.  The closed
immersion hypothesis is the typeclass `[hi : IsClosedImmersion i]`.  The
existentially chosen adjunction is `adj : tensorPullback i ⊣ pushforward i`.
For every module `F : Y.Modules`, `Epi (adj.unit.app F)` states that the unit
is an epimorphism (the categorical form of surjectivity of sheaf maps).  The
second conjunct states that the canonical cokernel presentation of this unit
is an isomorphism; its kernel is the submodule generated stalkwise by the
local products with the ideal sheaf `i.ker` (Mathlib's
`Scheme.Hom.ker`).  This is the categorical quotient form of
`F / JF ≅ i_* i^* F`, and the adjunction supplies naturality in `F`.
The proof is `sorry` as required for stage 2.

The declaration `IsClosedImmersion` is the Mathlib match for
`def-weil-closed-immersion`; `Scheme.Hom.ker` is the match for
`def-sbc-closed-immersion-ideal-sheaf`; `Scheme.Modules.tensorPullback` is
the recorded dependency declaration for `def-pc-module-pullback`; and
`SheafOfModules` tensor/change-of-rings definitions supply
`def-pur-sheaf-tensor-product`.

Edge cases checked: `Z = ⊥` (empty closed subscheme) gives the zero
pushforward and unit quotient by the unit ideal; `i = 𝟙 Y` gives the identity
unit and zero ideal; and the zero module gives the zero epimorphism and its
trivial cokernel.  No hypotheses on finiteness, noetherianity, or nonemptiness
were added.

Searches made before writing: `msearch.py leanfinder` for the closed-immersion
unit and ideal quotient (returned only closed-immersion and adjunction
infrastructure); `msearch.py loogle` for
`AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction` (returned the
abstract adjunction only); `rg` over Mathlib's AlgebraicGeometry/Modules and
project Sheaf sources (no declaration identifying the unit with a quotient by
an ideal sheaf); and `grep -rl` over `dag/nodes` for the target and its key
terms (no existing statement node).

## Earlier second reading (a previous round; superseded)

I reread the target node and the declaration line by line.  The explicit
`i : Z ⟶ Y` and `[IsClosedImmersion i]` are the node's closed-immersion data;
the existential adjunction is the pullback/pushforward adjunction; the
universal `F : Y.Modules` quantifier is present; `Epi` renders surjectivity;
and the `kernel`/`cokernel.desc` isomorphism renders the quotient by the
ideal-generated kernel.  The declaration has no extra finiteness or
separatedness assumptions, and its proof remains `sorry`.  I added the
blueprint identifier to the declaration docstring and synchronized the node's
recorded signature with the file.

## Second reading by M1

Independent reading of the node, the delivered file, and all five statement
 dependency nodes. The original worker report above describes the earlier
signature; the kernel and naturality assertions below supersede its claim
that they were already present.

Source reading: the repository's `literature/stacks-project` is absent on this
machine. I read the local Stacks .tex copy at
`/home/ubuntu/c1-stacks-review/spaces-morphisms.tex`, lines 2491 onward
(label `lemma-i-star-equivalence`, Tag 04CJ), and
`/home/ubuntu/c1-stacks-review/modules.tex`, lines 1945 onward
(the same label, Tag 08KS). The former is on small etale sites of algebraic
spaces over a scheme S; part (1) is the quotient assertion for every module,
not only quasi-coherent modules. The latter gives the ringed-space stalk
argument applicable to the node's Zariski scheme modules. It assumes only a
homeomorphism onto a closed subset and a surjective structure-sheaf map.
`IsClosedImmersion i` supplies both. The common base in the algebraic-space
statement adds no restriction to this ringed-space specialization. No
Noetherian, finite-type, separated-base, field, or characteristic hypothesis
is needed.

Object/hypothesis/conclusion checklist (the node's complete statement):

- Schemes Y and Z and their morphism i: rendered by
  `{Y Z : Scheme.{w}} (i : Z ⟶ Y)`. PASS. I read `def-pc-scheme` and
  Mathlib's `Scheme` and `Scheme.Hom`: these are schemes and their morphisms,
  not algebraic spaces or affine schemes.
- Closed immersion: `[IsClosedImmersion i]`. PASS. I read
  `def-weil-closed-immersion` and the Mathlib class, which includes closed
  embedding and surjectivity on stalks. No additional hypothesis appears.
- Defining ideal J = ker(O_Y → i_* O_Z): `i.ker.ideal V` on affine opens V.
  PASS. I read `def-sbc-closed-immersion-ideal-sheaf`, `Hom.ker`, and
  `Hom.ker_apply` in IdealSheaf/Basic.lean:692--704. For a closed immersion,
  quasi-compactness follows from affine-ness, so this ideal is exactly the
  kernel of `i.app V`. The node explicitly permits the affine-open
  description of the quasi-coherent ideal; local generation uses that
  description without creating a private ideal sheaf.
- Tensor-formula module pullback and module pushforward, with adjunction and
  unit: `∃ adj : tensorPullback i ⊣ pushforward i`, `adj.unit.app F`.
  PASS. I opened the recorded `TensorPullback.lean` dependency and
  `TensorPullbackAdjunction.lean`, and Mathlib's sectionwise `pushforward`.
  The former really uses change of rings on the abelian inverse image,
  not Mathlib's abstract `Modules.pullback`. The adjunction theorem pins a
  witness to the canonical tensor unit. The existential chooses one
  adjunction for all modules, not a different adjunction for each module.
  The properties are independent of adjunction choice: units for the same
  left and right adjoint differ by a natural automorphism of the target,
  preserving their kernels, epimorphism property, and quotient squares.
- Arbitrary O_Y-module F: `∀ (F : Y.Modules)`. PASS. There is no
  quasi-coherence, finite generation, flatness, or invertibility assumption.
- JF, the sheaf image of J tensor F → F, equivalently the subsheaf generated
  by products: the new local condition quantifies over every open U,
  every section m, and every point x in U, then requires an affine
  neighbourhood V ≤ U on which the restriction lies in
  `Submodule.span Γ(Y,V) {t | ∃ a, a ∈ i.ker.ideal V ∧ ∃ s, t = a • s}`.
  PASS. Spans are finite linear combinations, and coefficients can be
  absorbed into the ideal factor. This is precisely local membership in
  the sheaf image. Every neighbourhood can be refined to an affine one,
  so this basis choice imposes no extra hypothesis. Importantly this
  does not replace the sheaf image by a global sectionwise product.
  I opened `def-pur-sheaf-tensor-product` and its recorded TensorProduct
  module, including the imported source monoidal construction: the
  tensor is sheafification of the sectionwise tensor, which gives exactly
  this local image description. No new tensor definition is introduced.
- Surjectivity as a sheaf map: `Epi (adj.unit.app F)`. PASS. This is local
  surjectivity of module sheaves, not surjectivity of sections on each open.
- Kernel equals JF: the new iff
  `(adj.unit.app F).app U m = 0 ↔ ...local product condition...`.
  PASS. It covers all opens and sections, hence identifies the kernel
  subsheaf itself. This clause was MISSING in the original Lean: merely
  saying that an epi is the cokernel of its own kernel identifies no ideal.
- Canonical induced quotient isomorphism: the existing
  `IsIso (cokernel.desc (kernel.ι (adj.unit.app F)) (adj.unit.app F) ...)`.
  PASS after the new kernel identification: its source is now precisely
  F/JF, up to the canonical identification of kernel presentations. The
  descended morphism is induced by the same unit, not an unrelated iso.
- Naturality in F: the added final universal quantification over modules
  F,G and a morphism a gives qmap on cokernels with two commuting squares.
  The first square makes qmap the induced quotient map (uniquely, because
  the cokernel projection is epi); the second is the naturality square
  with `(tensorPullback i ⋙ pushforward i).map a`. PASS. This was previously
  asserted only in prose. The squares express a coherent natural
  transformation, since uniqueness forces identity and composition laws.

Edge cases: empty Y has only empty opens and the point condition is
vacuous, correctly giving the zero kernel condition on the zero section
module; empty Z gives J = O_Y and zero target, so locally the span is all
of F and F/JF = 0. For the identity immersion J = 0, the local span is
zero and the unit is an isomorphism. Zero F satisfies all clauses. No
index set or integer n occurs, so no empty-index or n=0 case is excluded.
All commutative stalk rings, including characteristic zero and positive
characteristic, are covered; no field is assumed. The universe w is bound
explicitly, schemes and modules are in its standard arbitrary universe,
and there is no hidden universe-zero specialization. Schemes of different
original size can be lifted to a common universe, as in the dependency.

Independent searches (2026-10-11):

- `msearch.py ... leanfinder "kernel of module pullback unit along closed
  embedding ideal generated submodule"`: eight hits, mostly
  IdealSheafData.ker_fst_of_isClosedImmersion, ker_subschemeι,
  ker_subschemeι_app, and ideal-ring kernel infrastructure; no module
  unit quotient statement.
- `msearch.py ... loogle "Submodule.span"`: twelve hits, including span,
  subset_span, span_empty, and span_eq; this existing Mathlib operation
  suffices for the inline local membership condition.
- `msearch.py ... leansearch "sheaf of modules kernel of adjunction unit
  quotient by ideal of closed immersion"`: service returned Internal
  Server Error / UNAVAILABLE. No mathematical verdict inferred from this.
- Independent `rg` searches for `idealProduct`, `idealMul`, `ideal.*smul`,
  `ideal.*tensor`, and `unit_quotient` across project Sheaf, the source
  WeilConjectures, and Mathlib module-sheaf files found no existing
  ideal-times-arbitrary-module or unit quotient declaration. They did
  find the source IdealSheaf/Module.lean bridge `IdealSheafData.toModules`
  and `toModulesι`; I opened it. It defines the ideal module and inclusion,
  not JF or this theorem. I do not duplicate it: the statement uses the
  recorded affine ideals directly and introduces no ideal-module object.
- Further `rg` for `kernel.*unit`, `unit.*kernel`, `quotient.*closed`,
  `closed.*quotient` in both AlgebraicGeometry trees found only unrelated
  curve/group statements and project citers of this node. No exact match.
  DAG search for the ideal-generated subsheaf found the present item and
  its ideal-sheaf dependency, not a separate existing product definition.

Changes: repaired H3 by adding the missing local kernel identification,
and made quotient naturality explicit. Replaced the compressed proof
summary with all six node proof steps and their cited dependency ids (H8).
Added the conventional copyright header and moved the module docstring
immediately after imports. Made all scheme, morphism, and instance binders
explicit in the declaration, and synchronized `lean.statement` verbatim.
The mathematical node statement and dependency list are unchanged; there
are no new nodes or dependency modules, and no `statement_change`.
There are no definitions, hence no hollow definitions. The only theorem
has the required `sorry` proof; the `by simp` terms in its type only certify
kernel-inclusion composites are zero for `cokernel.desc`. All lines are at
most 100 characters. Server `scompile.py` compiled the full delivered
module cleanly in 2.2 seconds (exit 0, no warnings).
