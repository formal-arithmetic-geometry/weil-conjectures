## Worker report

The module `Sheaf.AlgebraicGeometry.LocalOpenRepresentativesSupportDescent` states
`AlgebraicGeometry.localOpenRepresentatives_support_descent`. Its only proof is `sorry`.
No new notion, dependency repair, or statement correction is needed.

Clause-by-clause correspondence:

- The base scheme is `{T : Scheme.{u}}`. Explicit universes `u v w` implement
  `def-weil-size-convention`: schemes have universe u, the covering index has any
  universe v, and presheaf values lie in `Type (max u w)`.
- The category Sch/T is Mathlib's `Over T`, whose arrows are commuting triangles.
  `F : (Over T)ᵒᵖ ⥤ Type (max u w)` is an arbitrary set-valued presheaf.
- `{I : Type v}`, `{T' : I → Scheme.{u}}`, and `q : ∀ i, T' i ⟶ T`
  give the set-indexed family. `[∀ i, Etale (q i)]` gives its etaleness.
- `hq : ∀ t : T, ∃ (i : I) (x : T' i), q i x = t` is joint surjectivity,
  with no surjectivity assumption on the individual arrows.
- `W : ∀ i, (T' i).Opens` gives precisely the local open subschemes: Mathlib's
  `Scheme.Opens.toScheme` uses the restricted structure sheaf and `W.ι` is its inclusion.
- `α : ∀ i, uliftYoneda.{w}.obj (Over.mk (W i).ι) ≅ (Over.map (q i)).op ⋙ F`
  is the given natural isomorphism h_(W_i/T_i) ≅ F restricted to T_i.
  `Over.map` postcomposes structure morphisms by q_i. `uliftYoneda` is the existing
  Mathlib universe-lifted representable functor: its value is `ULift` of the set
  of T_i-morphisms into W_i. This is only the standard set-universe transport,
  allowing values in the larger chosen universe without identifying universes.
- The first conjunct, quantified over every i,j, equates
  `pullback.fst (q i) (q j) ⁻¹ᵁ W i` and
  `pullback.snd (q i) (q j) ⁻¹ᵁ W j` in the opens of the fibre product.
- The second conjunct `∃! U : T.Opens, ∀ i, (q i ⁻¹ᵁ U) = W i` states both
  existence and uniqueness of the descended open subscheme, including its restricted
  structure sheaf, since an open subscheme is encoded canonically by its open set.
- There is no sheaf, compatibility, finite-index, or quasi-compactness hypothesis.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  and `Scheme.Opens` (scheme dependency).
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`
  (etale-morphism dependency).
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`
  and its base-change instance; `Mathlib.AlgebraicGeometry.Restrict`:
  `Scheme.Opens.toScheme`, `Scheme.Opens.ι`, and its open-immersion instance.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `.fst`, `.snd`, and `.lift`;
  scheme pullbacks are supplied by `Mathlib.AlgebraicGeometry.Pullbacks`.
- `Mathlib.CategoryTheory.Comma.Over.Basic`: `CategoryTheory.Over.mk`, `Over.map`;
  `Mathlib.CategoryTheory.Yoneda`: `CategoryTheory.uliftYoneda`.
- Size convention is metatheoretic (its lean record explicitly has no declaration).
- Proof-only imports retain `Mathlib.AlgebraicGeometry.Sites.Fpqc`:
  `Scheme.fppfPrecoverage`, `Scheme.fppfPrecoverage_le_fpqcPrecoverage`
  (fppf-site and fppf-to-fpqc nodes), and
  `WeilConjectures.AlgebraicGeometry.FpqcOpenSubschemeDescent`:
  `AlgebraicGeometry.openSubscheme_existsUnique_of_fpqc`.
  Open-immersion base change is already provided by the statement imports.

Sources read: Stacks `spaces-descent.tex`, lemma-descending-property-open-immersion
(Tag 041X), and `descent.tex`, lemma-open-fpqc-covering (Tag 03N0).
The four-step proof docstring follows the accepted node proof, including its direct
presheaf-evaluation extension of the support argument; it does not descend F itself.

Edge cases checked before writing:

- If I is empty, hq forces T to have no points. Overlap equality is vacuous and
  there is exactly one open of T. There is no Nonempty or positive-cardinality binder.
- Empty local schemes and empty W_i are allowed. If all W_i are empty, the
  unique descended open is empty; if all W_i are full, it is the whole base.
- Repeated cover members and different choices of α_i do not impose a cocycle:
  evaluation on the overlap open gives the two inclusions regardless of α choices.
- Infinite covers and non-quasi-compact schemes are allowed. The proof uses the
  fppf-to-fpqc family comparison, not quasi-compactness of any q_i.
- Opens have their actual restricted structure sheaf, not an arbitrary scheme over
  the base. All variables and all universe levels in the signature are bound explicitly.

Searches made through the required `msearch.py` wrapper (2026-10-24):

- LeanFinder: “A presheaf on schemes over T represented by open subschemes on an
  etale cover has compatible supports descending to a unique open subset”. Eight
  hits, including LocalRepresentability.glueData_openCover_map, glueData_U, and
  glueData_J, directed gluing, and zero_of_zero_cover. No exact match.
- Loogle: `AlgebraicGeometry.IsOpenImmersion, CategoryTheory.yoneda`. Twelve hits
  in `Scheme.LocalRepresentability`; source read. These assume a Zariski sheaf
  and relatively representable maps and do not state this arbitrary-presheaf assertion.
- Grep: `open.*[Rr]epresent|descen.*open|open.*descen` in AlgebraicGeometry.
  Eight hits: Representability, FlatDescent, FlatMono, AffineTransitionLimit.
  They do not state this lemma. The fpqc open descent theorem itself exists and
  is imported as the node's proof dependency.
- LeanSearch: “Local open representatives of an arbitrary presheaf on schemes over
  a base have compatible inverse image opens along an etale covering and descend
  to a unique open subset”. Eight hits about topological sheaf conditions, etale
  topology, and scheme restriction; no exact match.
- Direct rg in both `lean/WeilConjectures` and `lean/Sheaf` for the node id and
  proposed declaration: no hits. Concept search for open representatives and open
  descent found existing open-descent and unrelated tensor/module comparison files,
  but no statement combining local presheaf representations and support descent.
  The upstream declaration-name index has no proposed-name or node-id match.

Validation: `scompile.py Q68 lem-trf-local-open-representatives-support-descent`
compiled both sandbox and intended library module cleanly (2.5 s and 1.8 s).
There are no disputed statements or node faults.

## Second reading by Q68

I reread the node and module together after compilation as a separate self-review
pass. This is not an independent worker review; the dispatcher prohibits starting
other agents and the delivery receives the maintainer's independent review.

The binders preserve the arbitrary presheaf on Sch/T, the jointly surjective etale
family, the open subschemes and each given natural isomorphism. In particular,
`Over.map (q i)` has domain Over(T_i), and its opposite precomposes F, so α's
right side is precisely the restriction in the node. The left side is the
representable of the open inclusion as an object of that same slice, lifted to
F's value universe. Both projections of the scheme pullback appear in the first
conjunct with the correct local opens. The second conjunct separately retains
unique existence and every inverse-image equality. No sheaf condition, cocycle,
finite-cover assumption, or quasi-compactness was added. The empty-index case
remains present. No mismatch was found and no statement correction was made.
