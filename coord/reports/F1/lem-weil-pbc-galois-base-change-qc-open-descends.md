## Worker report

The module `Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends` states
`AlgebraicGeometry.galois_baseChange_qc_open_descends`, with one `sorry` and no new
notions or definitions. The node copy changes only `lean`. No statement correction,
disputed statement, new node, or dependency repair was needed.

Source checked: Stacks Tag 04KU (https://stacks.math.columbia.edu/tag/04KU),
Tag 0388 (https://stacks.math.columbia.edu/tag/0388), and the preceding action equation
in `/home/ubuntu/c1-stacks-review/varieties.tex`, lines 850–897. The repository's
`literature/stacks-project/varieties.tex` is absent on this machine; the source is
available at the above local path and the official website. The node's strengthened
wording of (2), using the very same finite intermediate field as (1), is exactly the
subgroup used in the source proof.

Hypotheses and clauses, matched individually:

- A base field and field extension: `(k L : Type u) [Field k] [Field L] [Algebra k L]`.
  The map of the extension is `algebraMap k L`; field homomorphisms are injective.
- Galois, possibly infinite: `[IsGalois k L]`. Reading Mathlib's full definition shows
  that its two fields are `Algebra.IsSeparable k L` and `Normal k L`. The former
  includes algebraicity, exactly as recorded by def-weil-pbc-separable-algebraic-extension;
  the latter says every mapped minimal polynomial splits. There is no
  `FiniteDimensional k L` hypothesis.
- A scheme over k: `(X : Scheme.{u}) (f : X ⟶ Spec (.of k))`. An explicit structure
  map is used because the node concerns base change, as allowed by the standing brief.
- The scheme X_L: `pullback f (Spec.map (CommRingCat.ofHom (algebraMap k L)))`.
  This is the convention recorded by def-pc-base-change, not a new construction.
- The open V and its quasi-compactness: `V : (...).Opens` and `hV : IsCompact V.1`.
  Mathlib's `IsCompact` does not require Hausdorffness, and expresses quasi-compactness.
- The automorphism group Aut(L/k): `L ≃ₐ[k] L`.
- The induced map id_X × Spec(σ): the local let-binding
  `σX := fun σ : L ≃ₐ[k] L ↦ baseChangeMap f (specAlgEquivOver σ)`.
  `specAlgEquivOver` is the existing spectrum map of the algebra automorphism,
  bundled over Spec k; `baseChangeMap` is the existing map id_X × that morphism.
- Each induced scheme map is an automorphism: `∀ σ, IsIso (σX σ)`.
- Contravariant composition: `∀ σ τ, σX (σ * τ) = σX σ ≫ σX τ`.
  Mathlib's `AlgEquiv.mul_apply` says `(σ * τ) x = σ (τ x)`, while categorical
  `σX σ ≫ σX τ` means σX(τ) after σX(σ). Thus this is exactly
  `(σ ∘ τ)_X = τ_X ∘ σ_X`, with the required order.
- Part (1), subfield k ⊆ k' ⊆ L: `∃ K : IntermediateField k L`.
  The intermediate-field structure contains the base field and has a field subtype.
- Part (1), finite degree: `FiniteDimensional k K`, as a proposition in the conclusion,
  not an extra assumption on the extension.
- Part (1), descended open V' of X_K: `∃ V' : (pullback f
  (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Opens`, with `IsCompact V'.1`.
- Part (1), the canonical map p: `∃ p`, followed by the equality identifying it with
  `baseChangeMap f (Over.homMk (Spec.map (CommRingCat.ofHom K.toSubalgebra.val)) ...)`.
  `K.toSubalgebra.val` is precisely the inclusion K → L. Its compatibility with
  the base-field maps is definitional after `Spec.map_comp`; the short proof term
  solely constructs a morphism in the over category and proves none of the item.
- Part (1), descent equality: `V = p ⁻¹ᵁ V'`, equality of opens by inverse image.
- Part (2), the same K: inside that existential, quantify `∀ σ : L ≃ₐ[k] L`.
  The condition `∀ x : K, σ (x : L) = (x : L)` is pointwise fixing of K.
  The conclusion `(σX σ) '' V.1 = V.1` is the requested direct-image invariance.
  No normality of K/k, topology hypothesis, or unrelated choice of subgroup is added.

Dependency declarations read and used:

- def-pc-field-extension: `Algebra`, Mathlib.Algebra.Algebra.Defs;
  `algebraMap` and its field specialization.
- def-weil-pbc-separable-algebraic-extension: `Algebra.IsSeparable`,
  Mathlib.FieldTheory.Separable. Used through `IsGalois.to_isSeparable`;
  its `isAlgebraic` instance confirms the meaning of the node's dependency.
- def-weil-scheme-over-base: `Scheme.Over`, Mathlib.AlgebraicGeometry.Over;
  its structure map is represented explicitly by f, the same notion.
- def-pc-base-change: imported Sheaf.AlgebraicGeometry.BaseChangeConventions,
  whose docstring and full signatures prescribe `Limits.pullback f T.hom` and
  `AlgebraicGeometry.baseChangeMap` (WeilConjectures.AlgebraicGeometry.PicardFunctor).
  Its recorded main declaration `Scheme.Modules.moduleBaseChange` concerns modules;
  this item needs its recorded scheme-base-change convention, not module pullback.
- def-weil-affine-spectrum: `AlgebraicGeometry.Spec` and `Spec.map`,
  Mathlib.AlgebraicGeometry.Scheme, with `CommRingCat.ofHom`.
- Additional existing data constructors: `IntermediateField` and `toSubalgebra.val`
  (Mathlib.FieldTheory.IntermediateField.Basic); `IsGalois` and `Normal`
  (Mathlib.FieldTheory.Galois.Basic, Mathlib.FieldTheory.Normal.Defs);
  `specAlgEquivOver` (WeilConjectures.AlgebraicGeometry.Picard.Jacobian).
  The latter's complete implementation was read: its map is Spec of σ.toAlgHom.toRingHom,
  and its over-condition is σ.commutes. No definition is duplicated.

Edge cases checked before writing: empty X and empty V remain allowed (V' can be empty);
no quasi-compactness or quasi-separatedness of X is assumed, in agreement with Tag 0388;
the identity extension and degree-one intermediate field are allowed; L/k may have
infinite degree; there is no restriction on characteristic, perfectness, or algebraic
closedness of L. K/k need not be normal. All universes and variables are explicitly bound.
One universe for fields and schemes is the standard project convention; arbitrary sizes
can be accommodated at a common universe, and no smaller-universe quantification over
external test objects occurs.

Searches made with the required remote search tool:

- LeanFinder: `quasi compact open subset of a scheme base changed to a Galois field
  extension descends to a finite subextension`: 8 results, all about properness,
  compact fibres or quasi-compact morphisms; none states this descent theorem.
- Loogle: `IsGalois, IntermediateField`: 12 results about fixing subgroups, field
  towers and Galois correspondence. They supply the field language but no scheme-open descent.
- Mathlib grep: `galois|descend.*open` in AlgebraicGeometry: 19 hits, concerning
  ideal-sheaf Galois connections, affine transition limits or morphism flat descent;
  none matches this theorem.
- LeanSearch: `quasi compact open subset of scheme over infinite Galois extension
  descends to finite intermediate field`: service unavailable (Internal Server Error),
  recorded as unavailable in searches.jsonl.
- `rg` in WeilConjectures and lean/Sheaf for Galois, finite subextensions and open descent:
  found `specAlgEquivOver` and `baseChangeMap`, reused here, and
  `descend_qc_open_fg_subalgebra` (Tag 0388), which is the more general algebra descent
  used by the proof and does not state this node's finite-field and invariance clauses.
- Exact item-id search in WeilConjectures and exact declaration-name search in Mathlib,
  WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json: no match.

Validation: server single-file compile clean, exit 0, 2.4 seconds. The expected stage-2
proof remains `sorry`. The delivery dry run is run after preparing this report; the
independent second-reading section is left to the second reader.

## Second reading by F1

I independently opened the node statement and the Lean declaration and matched every
introduced object, hypothesis, and conclusion clause. The field objects `k` and `L`, their
`Field` and `Algebra` instances, and `[IsGalois k L]` render the field extension and its
separable algebraic normal (possibly infinite-degree) hypothesis. The explicit scheme
map `f : X ⟶ Spec (.of k)` renders a scheme over `k`; the pullback in `V` is exactly the
node's `X_{\bar k}` convention. `V` and `hV : IsCompact V.1` render the quasi-compact
open, including the empty-open case.

The `let σX` binding uses the existing `specAlgEquivOver` and `baseChangeMap`, hence is
precisely `id_X × Spec(σ)`. The first conjunction clause states `IsIso (σX σ)` for every
`σ`; the second states the contravariant composition law with the same multiplication
order as the node. The existential introduces an `IntermediateField k L` with
`FiniteDimensional k K`, then a quasi-compact open `V'` on the corresponding pullback.
It introduces `p` with the canonical inclusion-induced base-change map (the displayed
over-category compatibility proof only establishes that map's typing), and states
`V = p ⁻¹ᵁ V'`. Finally, in the same existential, it quantifies every automorphism fixing
`K` pointwise and states direct-image invariance `(σX σ) '' V.1 = V.1`, exactly the
node's clause (2). Quantifier nesting and conjunction association agree with the node.

No mismatch was found, so no Lean or node statement change was needed. Edge cases checked
again: empty `X` or `V`, identity and degree-one extensions, infinite degree `L/k`,
characteristic arbitrary, and non-normal intermediate `K`; none is excluded by the
binders. The universe choice is shared (`k`, `L`, and `Scheme.{u}`), with no independent
smaller test universe.

I rechecked the dependency records and declarations: `Algebra`/`algebraMap`,
`IsGalois`/`Algebra.IsSeparable`, explicit `Scheme.Over` convention, the pullback
base-change convention, and `Spec.map` are used directly or through the recorded
existing declarations. Searches (LeanFinder, Loogle, LeanSearch, and grep over Mathlib,
WeilConjectures, and Sheaf) found no existing declaration of this theorem; the existing
`specAlgEquivOver` and `baseChangeMap` are reused rather than duplicated. The module
compiles cleanly with `scompile.py`; its only proof placeholder is the required `sorry`.
