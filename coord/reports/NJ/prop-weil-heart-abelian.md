## Worker report

The module `Sheaf.CategoryTheory.Triangulated.TStructure.HeartAbelianKernelSplitting`
states the complete node as the single theorem
`CategoryTheory.Triangulated.TStructure.heart_abelian_and_idempotent_kernel_decomposition`.
Its proof is exactly `sorry`. No definitions, new nodes, dependency repairs, or statement
corrections are needed.

Hypotheses and clauses:
- An arbitrary triangulated category is `{C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C]`. These are precisely the ambient structures
  required by Mathlib's t-structure API, including the octahedral axiom.
- Its arbitrary t-structure is `(t : TStructure C)`. No boundedness, nondegeneracy,
  or idempotent completeness assumption occurs.
- The heart intersection is `t.heart.FullSubcategory`; Mathlib defines
  `t.heart = t.le 0 ⊓ t.ge 0`. The inherited category and preadditive structures are used.
- The heart is abelian is `Nonempty (Abelian t.heart.FullSubcategory)`. `Abelian` is
  structure-valued, so `Nonempty` expresses existence of the abelian structure as a
  proposition; it does not assume or choose any object or introduce a hollow definition.
- The supplementary assertion is stated for every abelian category, as the node says:
  `∀ (D : Type u') [Category.{v'} D] [Abelian D] (A : D) (e : A ⟶ A)`.
  Both universes are independent of the ambient triangulated category's universes.
- Idempotence is `e ≫ e = e`.
- The decomposition is `∃ φ : A ≅ (kernel e ⊞ kernel (𝟙 A - e))`.
- The inverse is the canonical map from the supplementary kernels:
  `φ.inv = biprod.desc (kernel.ι e) (kernel.ι (𝟙 A - e))`.
  This is the canonical maps clause in the blueprint proof, not an additional hypothesis.
- Carrying e to projection onto the second summand is
  `φ.inv ≫ e ≫ φ.hom = biprod.snd ≫ biprod.inr`.
  Lean composition is left-to-right. These are endomorphisms of the displayed biproduct.
  Applying this universally quantified clause to the abelian heart gives the stated
  consequence for every heart idempotent; no separate duplicate notion of splitting is needed.

Dependency declarations read and used:
- `def-weil-t-structure` is a Mathlib leaf: `CategoryTheory.Triangulated.TStructure` in
  `Mathlib.CategoryTheory.Triangulated.TStructure.Basic`, and `TStructure.heart` in
  `Mathlib.CategoryTheory.Triangulated.TStructure.Heart`. Read their full fields and
  signatures, including `Heart` and `hasHeartFullSubcategory`.
- `def-sp-abelian` is a Mathlib leaf: `CategoryTheory.Abelian` in
  `Mathlib.CategoryTheory.Abelian.Basic`. Read the class and the derived zero-object
  and finite-biproduct explanation. No dependency node needs a lean record.
- Proof dependencies are imported privately: extension closure from
  `Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE`, split distinguished
  biproduct triangles through `Mathlib.CategoryTheory.Triangulated.Pretriangulated`,
  and `AbelianSubcategory.abelian` from
  `Mathlib.CategoryTheory.Triangulated.TStructure.AbelianSubcategory`.
- The existing partial result `CategoryTheory.Triangulated.TStructure.abelianHeart`
  from `WeilConjectures.Mathlib.CategoryTheory.Triangulated.TStructure.Heart` is imported
  privately for the abelianity proof. Read the full module, including the generalized
  heart interface and `isIdempotentComplete_heart`. These do not assert the kernel
  decomposition and its projection equation, so an existing-only attachment would
  omit part of this node. The proof docstring includes all five DAG proof steps.

Edge cases checked mathematically before writing: e = 0 gives ker(0) ⊞ ker(1),
with zero second summand and zero second projection; e = 1 reverses this, giving
zero first summand and identity second projection. The zero object satisfies both.
An unbounded or degenerate t-structure remains allowed; its heart can be zero.
Neither the abelian category nor the ambient triangulated category is required small
or locally small in any fixed common universe. The supplementary clause specializes
back to the heart by its inherited category structure and the first conjunct.

Searches:
- `msearch.py ... leanfinder` query: "The heart of a t-structure is abelian and every
  idempotent is the projection onto the second summand of the kernels of e and identity
  minus e". Eight results, including `Idempotents.isIdempotentComplete_of_abelian`
  and `isIdempotentComplete_iff_idempotents_have_kernels`; none states every clause.
- `msearch.py ... loogle` query:
  `CategoryTheory.Triangulated.TStructure.abelianHeart, CategoryTheory.Idempotents.isIdempotentComplete_of_abelian`.
  Zero hits, unknown identifier for the upstream-only `abelianHeart`.
- `msearch.py ... grep` query `abelianHeart|idempotent.*kernel|kernel.*idempotent`
  in CategoryTheory: seven hits, general idempotent kernel criteria and splitting helpers.
- Direct Mathlib searches of TStructure and Idempotents; read
  `Preadditive/Biproducts.lean` splitting-bicone constructions. These supply general
  helpers, not the complete statement with the two specified kernels.
- Direct `rg` in upstream WeilConjectures and project lean/Sheaf for heart, Heart,
  abelianHeart, the blueprint id, and kernel/biproduct combinations. Found the existing
  abelianHeart and idempotent-completeness assertions, and unrelated kernel constructions.
  No full supplementary-kernel assertion was found. The new declaration name has
  no collision in upstream, project Lean, or dag/lean_names_upstream.json.

Read the original blueprint node and the local Stacks homology.tex
`lemma-idempotent-splitting` (Tag 0H9Q), which explicitly identifies the two kernels
as supplementary. The corrected source note already in the DAG is accurate;
there is no statement dispute. Compilation uses only the required server wrapper.

## Second reading by NJ

I independently read the repository node and sandbox Lean side by side, the
statement dependencies and all six proof-dependency records, BBD sections
1.2.0–1.2.4 and 1.3.1–1.3.6 (printed pages 27–31), and Stacks homology.tex,
lemma-idempotent-splitting (Tag 0H9Q), including its preceding kernel lemma.
The source has no boundedness or nondegeneracy assumption. The Stacks assertion
assumes only preadditivity and the indicated (co)kernels; the node deliberately
uses its abelian-category specialization, where both kernels exist.

Object/hypothesis/conclusion checklist (each verdict is pass):

1. Ambient triangulated category: `{C : Type u} [Category.{v} C]`,
   `[Preadditive C] [HasZeroObject C] [HasShift C ℤ]`, additive integer shifts,
   `[Pretriangulated C] [IsTriangulated C]`. I read Mathlib's `Pretriangulated`
   interface and `IsTriangulated.octahedron_axiom`: these are exactly the
   triangulated structures, without an additional finiteness hypothesis.
2. Arbitrary t-structure: `(t : TStructure C)`. I read Basic.lean's fields
   `le`, `ge`, shift stability, `zero'`, monotonicity, and
   `exists_triangle_zero_one`. This is the dependency's indexed encoding of
   the two aisles and their decomposition axiom. There is no boundedness binder.
3. Heart object: `t.heart.FullSubcategory`. I read Heart.lean's actual
   `heart := t.le 0 ⊓ t.ge 0` and `hasHeartFullSubcategory`; this is precisely
   the full intersection in the node, with the inherited morphisms.
4. Abelianity: `Nonempty (Abelian t.heart.FullSubcategory)`. I read
   `Abelian` in Abelian/Basic.lean: it extends Preadditive and normal mono/epi
   structures and supplies finite products, kernels and cokernels. Its finite
   products supply zero objects and biproducts. Nonempty makes this
   structure-valued conclusion propositional; it is not an assumed abelian
   structure or a definition with missing data.
5. Supplementary assertion in an arbitrary abelian category:
   `∀ (D : Type u') [Category.{v'} D] [Abelian D] (A : D) (e : A ⟶ A)`.
   This matches the node's general abelian-category clause, rather than merely
   a special endomorphism of a fixed heart. The category, object, then
   endomorphism are quantified in that order.
6. Idempotence hypothesis: `e ≫ e = e →`. This is precisely e²=e, with
   no splitness, mono/epi, characteristic or size assumption added.
7. Kernel decomposition: `∃ φ : A ≅ (kernel e ⊞ kernel (𝟙 A - e))`.
   Mathlib kernels and binary biproduct are used directly, with the stated
   order of the two summands. Abelianity supplies their existence.
8. Canonical structure maps:
   `φ.inv = biprod.desc (kernel.ι e) (kernel.ι (𝟙 A - e))`.
   This is the supplementary-kernel decomposition with the kernel inclusions,
   as in the node's final proof step and Stacks' specified structure maps;
   it is not an arbitrary choice of retract object or additional assumption.
9. Projection conclusion:
   `φ.inv ≫ e ≫ φ.hom = biprod.snd ≫ biprod.inr`.
   Both sides act on the displayed biproduct. With Lean's composition order,
   this is conjugation of e to diag(0,1), exactly the second projection.
   Universally specializing the second conjunct to the abelian heart yields
   every heart idempotent's splitting as claimed.

Edge cases: e=0 gives ker(0) ⊞ ker(1), with zero second projection; e=1 gives
ker(1) ⊞ ker(0), with identity second projection. The zero object and a zero
heart are covered, as are unbounded and degenerate t-structures. An empty
category cannot satisfy the ambient zero-object or abelian axioms, so is not a
missing case. No index set, scheme, degree parameter or coefficient field is
introduced. There is no characteristic restriction. Universes u,v,u',v' are
all explicitly bound and independent. When specializing to the heart, choose
u'=u and v'=v; the universal theorem introduces no common-universe restriction.

Independent duplicate searches, using words other than the first reader's:

- LeanFinder via msearch: "An idempotent endomorphism in an additive category
  decomposes its object into the kernels of the endomorphism and its
  complementary idempotent". Eight results include Karoubi.complement,
  Karoubi.decomposition and IsIdempotentComplete.idempotents_split. These concern
  the Karoubi envelope or unspecified retracts, not these two kernels.
- Loogle via msearch: `"kernel", "biprod"`. Results concern kernels of
  indexed biproduct projections and complementary subtype summands, not the
  asserted decomposition of an arbitrary idempotent.
- Grep via msearch: `supplementary|complementary.*kernel|kernel.*complementary`.
  Seven hits, none a category-theoretic statement of this assertion.
- Direct rg on Mathlib CategoryTheory/{Idempotents,Preadditive,Triangulated},
  upstream WeilConjectures, and project lean/Sheaf for kernels with identity,
  kernel/biprod combinations and heart abelianity. I opened the upstream
  TStructure/Heart.lean in full, including `abelianHeart` and
  `isIdempotentComplete_heart`, and Mathlib Preadditive/Biproducts.lean's
  splitting-bicone construction. The former prove abelianity and abstract
  splitting, while the latter supplies helpers for a split mono and a
  cokernel; none states the full node. Keeping this module does not create
  a second definition of any notion.

I also opened the proof interfaces `isLE₂`, `isGE₂`, `isLE_of_isZero`,
`isGE_of_isZero`, `binaryBiproductTriangle_distinguished`,
`AbelianSubcategory.admissibleMorphism` and `AbelianSubcategory.abelian`.
Their hypotheses and cone-shift conventions match the proof docstring and
DAG plan. The public imports supply the statement's objects; private imports
supply the recorded proof interfaces and existing partial result.

No mathematical or convention mismatch was found. No Lean, node statement,
dependency record or definition was changed; this second-reading report is
the only addition. There are no new nodes, dependency modules or statement
corrections to audit. The sole theorem retains exactly `sorry`, and no data
definition is introduced. The source/blueprint docstrings carry all five
proof steps, including construction of p,q and all four matrix identities.
Every line is at most 100 characters and the node's lean.statement equals
the file's signature verbatim. Server scompile.py compiled the delivered
file cleanly (sandbox and library checks, 1.1 seconds each), without warnings.
