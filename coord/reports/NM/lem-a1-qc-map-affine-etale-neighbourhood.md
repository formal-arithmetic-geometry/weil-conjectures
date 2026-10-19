## Worker report

The module `Sheaf.SecPurity.QcMapAffineEtaleNeighbourhood` states
`AlgebraicGeometry.AlgebraicSpace.exists_affine_etale_neighbourhood` for a scheme `S`, an
algebraic space `E : AlgebraicSpace S`, a quasi-compact `S`-scheme `C : Over S` (rendered
by `[CompactSpace C.left]`), and an `S`-map `c : yoneda.obj C ⟶ E.obj.obj`.  Its conclusion
is an affine `U : Over S`, a map `u : yoneda.obj U ⟶ E.obj.obj`, and a representing scheme
`V : Over S` with `p : V ⟶ C` and `q : yoneda.obj V ⟶ yoneda.obj U`.

The hypotheses and clauses are rendered as follows.

* `S` is `{S : Scheme.{u}}`; `E` is `AlgebraicSpace S`; `C` is `Over S` and hence a
  scheme over `S`; quasi-compactness is `[CompactSpace C.left]`, the recorded Mathlib
  interpretation of `def-weil-pbc-quasi-compact-scheme`; and `c` is the natural
  transformation `yoneda.obj C ⟶ E.obj.obj`.
* `U` is an `Over S` and `IsAffine U.left` expresses that its underlying scheme is affine.
* `u : yoneda.obj U ⟶ E.obj.obj` is the scheme chart; `IsEtale u` is the recorded
  `AlgebraicSpace.IsEtale`, i.e. representable and étale after every scheme base change.
* `V : Over S`, `p : V ⟶ C`, and `q : yoneda.obj V ⟶ yoneda.obj U` are accompanied by
  `IsPullback q (yoneda.map p) u c`, which identifies `yoneda.obj V` with the sheaf fibre
  product and `p` with its projection to `C`.
* `Surjective p.left`, `Etale p.left`, `IsSeparated p.left`, and
  `Scheme.Hom.IsLocallyQuasiFinite p.left` state respectively surjectivity, étaleness,
  separatedness, and local quasi-finiteness of that projection.  No quasi-compactness of
  `p` or of `E` or `S` is added.

The statement uses these dependency declarations:

* `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme` (and `Scheme.Hom`) for
  schemes and morphisms;
* `Sheaf.AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicGeometry.AlgebraicSpace`, `AlgebraicSpace.IsEtale`, and
  `AlgebraicSpace.IsRepresentableWith` for algebraic spaces and representable étale maps;
* `Mathlib.Topology.Defs.Filter`, `CompactSpace` for quasi-compactness;
* `Mathlib.AlgebraicGeometry.Morphisms.Etale`, `AlgebraicGeometry.Etale` for scheme étaleness;
* `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `AlgebraicGeometry.IsSeparated` for separated
  scheme morphisms; and
* `Sheaf.AlgebraicGeometry.QuasiFiniteMorphism`,
  `AlgebraicGeometry.Scheme.Hom.IsLocallyQuasiFinite` for the Stacks local
  quasi-finiteness notion.

Edge cases checked against the source statement include an empty `C` (the CompactSpace
hypothesis permits it and the existential chart may have an empty pullback), an empty affine
chart fibre, and the absence of any separatedness or quasi-compactness assumption on `E` or
`S`.  The formulation does not require `p` itself to be quasi-compact, matching the node.

Searches for an existing declaration were made with:

* `msearch.py ... leanfinder "affine etale neighbourhood of a quasi compact scheme map to an
  algebraic space"`:
  eight hits, including generic Mathlib affine-cover and étale declarations but no algebraic-space
  neighbourhood theorem;
* `msearch.py ... loogle "AlgebraicGeometry.AlgebraicSpace.IsEtale, IsAffine, IsPullback,
  IsLocallyQuasiFinite"`:
  no hits (the identifier was not known to Loogle);
* `msearch.py ... grep "affine.*etale.*neighbourhood|exists_affine_etale_neighbourhood" Mathlib/`:
  no hits; and
* `rg` over `WeilConjectures/` and `lean/Sheaf/` for the theorem name and the corresponding
  affine-etale-neighbourhood pattern: no existing declaration (only textual references to this
  blueprint item and unrelated neighbourhood lemmas).

The generic Mathlib hit `Scheme.exists_hom_isAffine_of_isLocalAtSource` only concerns a
scheme-to-scheme morphism and cannot state a map to an algebraic space, so it is not a duplicate.

## Second reading by NM

I reread the node and the complete declaration.  The node's hypotheses appear in the same order:
`S` is a scheme, `E` an algebraic space over `S`, `C` an `S`-scheme with the exact
quasi-compact `CompactSpace` assumption, and `c` an `S`-map.  The conclusion has exactly the
node's affine `U`, representable étale chart `u`, and the scheme fibre-product projection,
with each of the four requested properties.  `IsPullback` supplies the fibre-product
identification rather than introducing an unrelated map.  No hypothesis or conclusion clause
was added or omitted, and no statement correction or `STATEMENT-DISPUTED` flag is needed.
