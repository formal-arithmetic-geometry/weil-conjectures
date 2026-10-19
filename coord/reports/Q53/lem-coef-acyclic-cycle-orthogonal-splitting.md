## Worker report

The module `Sheaf.Algebra.Homology.AcyclicCycleOrthogonalSplitting` states
`CochainComplex.exists_section_of_acyclic_cycles_orthogonal`. Its only theorem has proof
`sorry`; its docstring gives all eight steps of the node's proof. There are no new
notions, helper declarations, dependency repairs, or statement corrections. The node copy
changes only `lean`.

Hypothesis and conclusion correspondence:

| Node clause | Lean rendering |
| --- | --- |
| An arbitrary abelian category A | `{A : Type u} [Category.{v} A] [Abelian A]`; both universes are explicit and independent. |
| Integer cochain complexes X and Y, with consecutive differentials composing to zero | `(X Y : CochainComplex A ℤ)`; `HomologicalComplex.d_comp_d` is part of this standard complex structure. |
| ZⁿX and ZⁿY are the kernels of the outgoing differentials | `X.cycles i` and `Y.cycles j`; `HomologicalComplex.cyclesIsKernel` identifies their inclusions as the kernels of `d i (i + 1)`. |
| Both complexes are acyclic, image equals kernel in every degree | `(hX : X.Acyclic) (hY : Y.Acyclic)`; `Acyclic` is exactness at every index, `ExactAt` uses `ShortComplex.Exact`, and `ShortComplex.exact_iff_image_eq_kernel` identifies exactness with the stated equality of subobjects. |
| Every extension of ZⁱX by ZʲY splits, for every integer i,j | `(horth : ∀ i j : ℤ, Cotorsion.ExtOneOrthogonal (X.cycles i) (Y.cycles j))`. The existing predicate quantifies over all middle objects and arrows, requires `ShortComplex.ShortExact`, and concludes `IsSplitEpi` of the quotient. This is precisely the node's specified splitting interpretation of Ext¹ vanishing. |
| Every short exact extension 0 → Y → E → X → 0 in cochain complexes | Arbitrary `(E : CochainComplex A ℤ) (ι : Y ⟶ E) (p : E ⟶ X) (w : ι ≫ p = 0)` and `(hseq : (ShortComplex.mk ι p w).ShortExact)`. Short exactness includes exactness, monicity of ι and epicity of p. The four binders parameterize every such extension; E is not assumed acyclic separately. |
| A cochain section s : X → E with ps = identity | `∃ s : X ⟶ E, s ≫ p = 𝟙 X`; the morphism type requires differential compatibility. Lean composition is in diagrammatic order. |

Dependency declarations read and used:

- `def-sp-abelian`: `CategoryTheory.Abelian` in
  `Mathlib.CategoryTheory.Abelian.Basic`; read its full class and docstring.
- `def-weil-pbc-exact-sequence`: `CategoryTheory.ComposableArrows.Exact` in
  `Mathlib.Algebra.Homology.ExactSequence` and `CategoryTheory.ShortComplex.Exact` /
  `CategoryTheory.ShortComplex.ShortExact` in the recorded short-complex modules.
  The recorded `ExactSequence` module is imported publicly; the theorem directly uses
  the recorded `ShortExact` declaration, available through `HomologicalComplexAbelian`.
- The shared `CategoryTheory.Cotorsion.ExtOneOrthogonal` from
  `Sheaf.CategoryTheory.SmallCotorsionModelRecognition` is imported publicly because
  it occurs in the signature. Its full definition was read: it says every extension
  admits a section. It has only an abelian-category hypothesis, despite the larger
  recognition theorem in its owning module. `IsSplitEpi` and `SplitEpi` were also read
  in `Mathlib.CategoryTheory.EpiMono` to check the direction of the section equation.
- Proof dependency `lem-coef-cotorsion-orthogonality-calculus`:
  `CategoryTheory.cotorsion_orthogonality_calculus` in
  `Sheaf.CategoryTheory.CotorsionOrthogonalityCalculus`; its full signature and proof
  docstring were read. Its module is a non-public import for the future proof.
- Proof dependency `lem-weil-pbc-abelian-exact-epi-cokernel` is a Mathlib leaf whose
  recorded declaration is `CategoryTheory.ShortComplex.Exact.gIsCokernel` in
  `Mathlib.Algebra.Homology.ShortComplex.Exact`, already imported transitively.
  Its cokernel signature and docstring were read, along with `Exact.fIsKernel`.
- Standard complex declarations were read in
  `Mathlib.Algebra.Homology.HomologicalComplex` and
  `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`: `CochainComplex`,
  `HomologicalComplex.Hom`, `cycles`, `cyclesIsKernel`, `ExactAt`, and `Acyclic`.
  `Mathlib.Algebra.Homology.HomologicalComplexAbelian` supplies the abelian category
  of complexes and equivalence between categorical and degreewise short exactness.

Source grounding: read the entire recorded master blueprint statement and proof at
`sec-six-functors/sk-prop-sf-biduality-general/prop-coef-integral-exceptional-adjoint.md`
and the current `main-20261015` proof at
`sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`.
This node is explicitly an agent-formulated general tool for the derived coefficient
adjunction paragraph, not a claim that the blueprint states this general lemma verbatim.
Its recorded proof uses extension closure, kernel/cokernel properties, and three fillers.
The Lean theorem states exactly that general tool and adds no geometric assumptions.

Edge cases checked before writing:

- X = 0: the unique zero cochain map to E is a section, since the identity of zero is zero.
- Y = 0: a short exact quotient p is an isomorphism, so its inverse is a cochain section.
- Both zero, the zero category, and acyclic complexes with zero terms remain included.
- There is no boundedness restriction, initial degree, finiteness assumption, or choice
  of projective/injective resolutions. Both positive and negative integer degrees are
  covered. The two-pass construction chooses independently in every degree.
- The original cycle hypothesis quantifies over all pairs of degrees, including equal
  and adjacent degrees. No weaker same-degree-only condition was substituted.
- No `HasExt`, enough-injectives, enough-projectives, Grothendieck, local-smallness,
  or equality of universes is imposed. Splitting orthogonality uses the already shared
  predicate, with its quotient/subobject order checked against the node.
- Choosing Mathlib's canonical cycles does not restrict the kernel: their inclusions
  satisfy the kernel universal property, hence are canonically isomorphic to any
  other kernel choice. The splitting condition is invariant under these isomorphisms.

Searches for an existing theorem (2026-10-16):

- `msearch.py leansearch`, query
  `Ext orthogonal cycles of acyclic complexes imply all short exact extensions split`:
  8 hits, including `ShortComplex.Splitting.ofExactOfSection`, generic splittings and
  K-projective orthogonality. None constructs a cochain section from cycle orthogonality.
- `msearch.py leanfinder`, query
  `Every short exact extension of two acyclic cochain complexes splits when every extension between their cycles splits`:
  8 hits, including `CochainComplex.homOfDegreewiseSplit`,
  `CochainComplex.cocycleOfDegreewiseSplit`, mapping-cone splittings, and derived Ext
  exact sequences. None states this lemma; degreewise-split constructions consume
  chosen splittings and do not supply the two-pass cochain correction.
- `msearch.py loogle`, query `"HomologicalComplex", "Splitting"`: 0 hits.
- `msearch.py grep`, query
  `(cycle|cycles).*(orthogonal|splitting)|Ext.*(cycle|cycles)` in `Algebra/Homology`:
  25 hits, consisting of generic cycle/opcycle extensionality, spectral cycles and
  degreewise-split cocycle formulas. No matching theorem.
- `rg` over upstream `WeilConjectures/` and side `lean/Sheaf/`, query
  `acyclic.*(split|orthogonal)|cycle.*orthogonal|ExtOneOrthogonal`: no upstream match;
  side results locate the existing splitting predicate, its calculus, downstream
  `HereditaryCotorsionComplexLift`, and unrelated acyclic-lifting lemmas.
- Searched the item id in upstream `WeilConjectures/` and `dag/lean_names_upstream.json`:
  no existing declaration. Searched the proposed full theorem name in Mathlib,
  upstream, side sources and the upstream name index: no collision.

Validation: the prescribed `scompile.py` invocation returned exit 0 with no errors or
warnings. It checked the sandbox file (6.9 seconds) and its library module path
(4.7 seconds), each under the normal 60-second limit. The first compile identified
a missing direct import of `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`;
adding that import supplies the actual cycles and acyclicity declarations and produced
the clean final compile. The required `deliver2.py --no-push` dry run is also run before
returning READY. No statement dispute or node fault was found.

## Second reading by Q53

I reread the node statement, its source place, the dependency declarations, and
`Sheaf/Algebra/Homology/AcyclicCycleOrthogonalSplitting.lean` independently.

The node's objects and hypotheses match the file as follows:

1. The abelian category `\mathcal A` is `{A : Type u} [Category.{v} A] [Abelian A]`.
   Both category and object universes are explicit; no equality or finiteness condition
   is added. Verdict: exact.
2. The integer cochain complexes are `(X Y : CochainComplex A ℤ)`. This is the
   standard complex with its consecutive differential condition built into the object.
   Verdict: exact.
3. The cycle objects `Z^nX` and `Z^nY` are `X.cycles n` and `Y.cycles n`, with the
   canonical kernel inclusions supplied by `cyclesIsKernel`. Verdict: exact.
4. Acyclicity is `(hX : X.Acyclic) (hY : Y.Acyclic)`, namely exactness at every
   integer degree and therefore image of the preceding differential equal to the next
   kernel. Verdict: exact.
5. Cycle Ext-one vanishing is
   `horth : ∀ i j : ℤ, Cotorsion.ExtOneOrthogonal (X.cycles i) (Y.cycles j)`.
   The recorded definition quantifies over every middle object, maps, zero composite,
   and `ShortExact`, and requires `IsSplitEpi` of the quotient; this is precisely the
   node's stated splitting meaning. Verdict: exact, with all integer pairs included.
6. An arbitrary short exact complex extension is represented by
   `(E : CochainComplex A ℤ) (ι : Y ⟶ E) (p : E ⟶ X)`,
   `w : ι ≫ p = 0`, and `(ShortComplex.mk ι p w).ShortExact`. The maps are cochain
   maps and short exactness is in the category of cochain complexes, so no termwise or
   acyclicity assumption was added. Verdict: exact.
7. The required conclusion is `∃ s : X ⟶ E, s ≫ p = 𝟙 X`, a cochain section in
   the same composition convention as the node. Verdict: exact; no stronger
   retraction or uniqueness clause appears.

The source place calls this an agent-formulated general extension tool for the derived
coefficient-adjunction proof paragraph. It imposes no geometric hypotheses, bounds, or
resolution assumptions. The file follows that scope. I found no mismatch and changed
nothing in the statement or module.

Edge cases checked: zero `X`, zero `Y`, both zero, a zero abelian category, arbitrary
positive and negative integer degrees, equal or adjacent cycle indices, and complexes
with zero terms are all admitted. The independent universes `u` and `v` do not exclude
any source case. No empty-index issue occurs because the index is all of `ℤ`.

Searches were repeated with LeanSearch for orthogonal-cycle splitting, LeanFinder for
short exact extensions of acyclic cochain complexes, Loogle for `HomologicalComplex`
and `Splitting`, grep through Mathlib homology sources for cycle/orthogonality and
cycle/Ext names, and `rg` through upstream `WeilConjectures/` and project `lean/Sheaf`.
The results were generic splitting or degreewise-split constructions and the existing
orthogonality predicate, with no declaration of this theorem. The item id and proposed
full declaration name also have no upstream or Mathlib collision. Therefore no existing
record, dependency module, new definition node, or statement correction is needed.

The required `scompile.py` check passes with no errors or warnings.
