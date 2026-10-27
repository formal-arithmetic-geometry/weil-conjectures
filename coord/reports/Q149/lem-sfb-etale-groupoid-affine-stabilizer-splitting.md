## Worker report

The delivery states `AlgebraicGeometry.IsGroupoidScheme.exists_affine_etale_stabilizer_splitting`
in `Sheaf.AlgebraicGeometry.EtaleGroupoidAffineStabilizerSplitting`. Its only proof is `sorry`.
There are no new definitions, new nodes, dependency repairs or statement corrections.
Only the item's `lean` record changes. The signature is copied verbatim into that record.

Sources read: `literature/stacks-project/spaces-more-groupoids.tex`,
`definition-split-at-point` (04RK), `situation-splitting` (0DTB),
`lemma-splitting-scheme` (0DTD), `lemma-strong-splitting-affine-scheme` (04RZ),
and `lemma-splitting-affine-scheme` (0DTE). The last lemma uses exactly the proof of
04RZ with splitting substituted for strong splitting. The node intentionally assumes
local quasi-finiteness everywhere and finite stabilizer fibre, as its source record says;
these hypotheses are retained verbatim in mathematical meaning.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node | Lean |
| --- | --- |
| Schemes and size convention | `{S V R : Scheme.{u}}`, explicit `universe u`; all witnesses and test schemes for `IsGroupoidScheme` have this universe. |
| Groupoid scheme over `S` | `p : V ⟶ S`, `s t`, `e`, `i`, `c`, `hG : IsGroupoidScheme s t e i c`, and `hp : s ≫ p = t ≫ p`. The structure map of `R` is `s ≫ p`; `hp` also makes it `t ≫ p`. The groupoid laws then make unit, inverse and composition morphisms over `S`. This exposes the base compatibility implicit in the node, using the recorded absolute groupoid interface, without changing it. |
| `V` affine | `[IsAffine V]`. Mathlib's affineness means isomorphic to a spectrum. |
| Source and target separated, with the stated meaning | `[IsClosedImmersion (pullback.diagonal s)]` and the same for `t`. |
| Source and target flat | `[Flat s] [Flat t]`. |
| Source and target locally of finite presentation | `[LocallyOfFinitePresentation s] [LocallyOfFinitePresentation t]`. |
| Source and target locally quasi-finite in the Stacks sense | `hqs : s.IsLocallyQuasiFinite`, `hqt : t.IsLocallyQuasiFinite`, from the recorded upstream interface, including its local-finite-type requirement. |
| Specified point | `v : V`. |
| Stabilizer `G` and its fibre finite over the residue field | `equalizer s t` is the scheme of arrows whose source and target morphisms agree, with map `equalizer.ι s t ≫ s` to `V`. The hypothesis is `[IsFinite ((equalizer.ι s t ≫ s).fiberToSpecResidueField v)]`. This is the full scheme-theoretic fibre over `Spec κ(v)`. |
| Affine etale `S`-scheme `V'` and map to `V` | Existentials `V' : Scheme.{u}`, `h : V' ⟶ V`, with `IsAffine V' ∧ Etale h`. Its structural map to `S` is the specified composite `h ≫ p`. |
| Point over `v` with unchanged induced residue field | `v' : V'`, `h v' = v`, `IsIso (h.residueFieldMap v')`. This concerns the induced map, rather than an arbitrary field isomorphism. |
| The actual restriction `R ×_(V ×_S V) (V' ×_S V')` | `IsPullback a b s h` identifies `A` with `R ×_(s,V,h) V'`, and `IsPullback r t' (a ≫ t) h` identifies `R'` with `A ×_(a ≫ t,V,h) V'`. Thus source, target and arrow projection are respectively `r ≫ b`, `t'`, `r ≫ a`. These are universal cartesian squares, not hypotheses on an arbitrary replacement arrow map. |
| Induced groupoid operations | Existential `e' i' c'` with `IsGroupoidScheme (r ≫ b) t' e' i' c'`, the endpoint squares `hs ht`, and the three equations commuting with the original unit, inverse and composition. `pullback.map` is Mathlib's induced map on composable pairs. The pullback universal properties uniquely determine these induced operations from these equations and endpoints. |
| Open subscheme with restricted structure sheaf | `P : R'.Opens`, `P.toScheme`, and its canonical open immersion `P.ι`. |
| Contains the whole unit | `eP : V' ⟶ P.toScheme`, `eP ≫ P.ι = e'`. |
| Stable under inverse | `iP : P.toScheme ⟶ P.toScheme`, `iP ≫ P.ι = P.ι ≫ i'`. |
| Stable under composition | `cP` on `pullback (P.ι ≫ (r ≫ b)) (P.ι ≫ t')` and the equation `cP ≫ P.ι = pullback.map ... ≫ c'`. The object map is the identity, so this restricts composition on every composable pair in `P`. |
| Groupoid on the same objects | `IsGroupoidScheme (P.ι ≫ (r ≫ b)) (P.ι ≫ t') eP iP cP`, whose object scheme is precisely `V'`. |
| Both restricted projections finite locally free | `(P.ι ≫ (r ≫ b)).IsFiniteLocallyFree ∧ (P.ι ≫ t').IsFiniteLocallyFree`, using the recorded class, exactly finite + flat + locally of finite presentation. |
| Every point of `G'_{v'}` lies in `P` | Final universal quantifier over `(equalizer.ι (r ≫ b) t' ≫ (r ≫ b)).fiber v'`. Its image through `fiberι` and the equalizer inclusion belongs to `P`. |
| Equivalent scheme equality after pulling back `P` | The preceding condition says the inverse image open of `P` in the whole stabilizer fibre is top. Since this is an open restriction with its restricted structure sheaf, its inclusion is an isomorphism of schemes, including nilpotent structure. This is exactly the equivalently stated equality in the node; no condition on just the unit or on only set-theoretic endpoint fibres is substituted. |

The two standard universal-property presentations used here introduce no new notion.
For every test scheme `T`, maps to `equalizer s t` are exactly maps `a : T ⟶ R`
with `a ≫ s = a ≫ t`. Maps to `R ×_(V ×_S V) V` are the same data, with the
map to `V` forced to be that common composite. This proves that the equalizer is
canonically the stabilizer appearing in the node, with its correct structural map.
Similarly the two cartesian squares for `A,R'` classify triples `(a,x,y)` with
`a ≫ s = x ≫ h` and `a ≫ t = y ≫ h`. Base compatibility `hp` then forces
`x ≫ h ≫ p = y ≫ h ≫ p`, so these triples are exactly the points of the stated
double base change. This remains valid for nonreduced test schemes and nonseparated bases.
The existential presentation of the pullbacks is equivalent to using the chosen
Mathlib pullbacks by their unique compatible isomorphism.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`;
  Mathlib affineness is `AlgebraicGeometry.IsAffine`.
- `def-weil-size-convention`: its recorded convention has no declaration;
  realized by explicit universe binders.
- `Sheaf.AlgebraicGeometry.GroupoidScheme`: `AlgebraicGeometry.IsGroupoidScheme`,
  including all eleven fields and their source docstring.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism`:
  `AlgebraicGeometry.Scheme.Hom.IsLocallyQuasiFinite`, and its defining
  `IsQuasiFiniteAtPoint`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `AlgebraicGeometry.Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback` and
  `Mathlib.AlgebraicGeometry.Limits`: `pullback`, its projections and maps, and
  finite limits of schemes; `CategoryTheory.IsPullback` specifies their universal property.
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`:
  `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFree`, whose three parent classes were read.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`,
  instantiated by the canonical open-scheme inclusion `P.ι`.
- Additional standard constructions: `equalizer`, `equalizer.ι` from Mathlib equalizers;
  `Scheme.Hom.fiber`, `fiberι`, `fiberToSpecResidueField` from
  `Mathlib.AlgebraicGeometry.Fiber`.

Every already-recorded non-Mathlib proof-dependency module is imported as a proof import:
`GroupoidInvariantOpenRestrictionDegree`, `LocallyOfFiniteTypeOfIsLocallyQuasiFinite`,
`QuasiFiniteAtPointIsolated`, `SeparatedLqfBaseChange`, and `UnramifiedQuasiFinite`.
The Mathlib proof dependencies are available through the listed statement imports
and plain proof imports `Morphisms.Proper`, `Morphisms.QuasiSeparated` and `PullbackCarrier`.
The four unstated scheme-groupoid proof lemmas have no recorded declarations to import;
they are retained in the node and explicitly named in the six-step proof docstring.

Edge cases checked before writing and again against the completed signature:

- Empty `V` is vacuous because a point `v : V` is supplied. No independent nonemptiness
  restriction is added. An empty arrow scheme with nonempty `V` cannot satisfy the unit laws.
- For the identity groupoid the stabilizer is `V`, its fibre is `Spec κ(v)`, and
  taking `h = 𝟙 V`, the canonical pullbacks and `P = ⊤` gives the claimed form.
- For a finite locally free group scheme over a field (one object), the entire arrow
  scheme is an allowed `P`; the theorem does not require the group to be reduced or etale.
- The last condition applies to the fibre of the equalizer structural map, not to all
  arrows whose underlying source and target points are `v'`. This retains splitting,
  rather than the stronger strong-splitting condition distinguished in 04RK.
- Nonreduced stabilizers and nonclosed points are included by scheme-theoretic fibres
  and the actual induced residue-field map. No closed-point, geometric-point,
  separability, characteristic, Noetherian or quasi-compactness assumption is added.
- No affineness or separation assumption is made on `S`. The equalizer and the
  iterated pullback descriptions follow from universal properties over arbitrary `S`.
- All universe variables and all term variables are explicit; no file-local definitions,
  notations, instances, `let` binders or automatic implicit variables are used.

Searches actually run, all on 2026-10-24:

1. `msearch.py ... leanfinder "Affine etale splitting of a flat separated locally
   finitely presented locally quasi finite scheme groupoid at a finite stabilizer"`:
   eight hits, including `Scheme.Etale`, `IsEtale`, ordinary etale morphism properties
   and etale algebra splitting; none states the groupoid-splitting conclusion.
2. `msearch.py ... loogle "AlgebraicGeometry.IsGroupoidScheme, CategoryTheory.IsPullback"`:
   zero hits; Loogle reports unknown identifier `AlgebraicGeometry.IsGroupoidScheme`
   (a project declaration). This query supplies no Mathlib match.
3. `msearch.py ... grep "stabilizer|GroupoidScheme|groupoid" AlgebraicGeometry`:
   zero Mathlib hits.
4. `msearch.py ... leansearch "A scheme groupoid with finite stabilizer admits affine
   etale localization and an open finite locally free subgroupoid"`: eight hits,
   including finite discrete affine schemes, `LocallyQuasiFinite`, `IsAffineOpen`,
   smoothness implying finite presentation and ordinary category localization;
   no groupoid splitting statement.
5. `rg -n "stabilizer|Stabilizer|GroupoidScheme|groupoid"` in the specified project's
   `lean/WeilConjectures/AlgebraicGeometry` and `lean/Sheaf/AlgebraicGeometry`:
   found the recorded groupoid interface, presheaf stabilizers for algebraic spaces,
   invariant-open restriction and unrelated affine-invariant comparison results.
   The presheaf algebraic-space stabilizer has different input data, not a duplicate
   of a scheme construction needed here. Standard scheme equalizers suffice inline.
6. `rg -n "lem-sfb-etale-groupoid-affine-stabilizer-splitting" lean/WeilConjectures`:
   no match. Additional searches for `splitting|finite_part|finitePart|stabilizer.*split`
   found no existing statement of this node.
7. `rg -n "exists_affine_etale_stabilizer_splitting"` in
   `dag/lean_names_upstream.json`, `lean/WeilConjectures` and `lean/Sheaf`: no name clash.

Validation: the prescribed `scompile.py Q149 <item> <module>` compiled both its private
sandbox module and the library-named module cleanly, each reported at 1.6 seconds,
with exit status 0 and no diagnostics. No global build or direct git command was run.
No `STATEMENT-DISPUTED` issue or node fault was found.

## Second reading by Q149

I reread the node, source and completed signature in a separate pass; no second agent
was started, as instructed. The maintainer supplies the independent review.

The main risk checked was accidentally stating strong splitting. The final domain is
the fibre of the scheme equalizer, so it is exactly the stabilizer fibre required by
04RK(2), not the set of all topological loops used in 04RK(1). The unit clause is
separately enforced by its factorization through `P`. Inverse and composition are
restrictions of the induced operations, with a full `IsGroupoidScheme` on the unchanged
object scheme. Both finite locally free clauses use the existing three-condition class.

I checked both cartesian squares in order: `a,b` pull back `s,h`; `r,t'` then pull back
`a ≫ t,h`. Thus the source is `r ≫ b` and target is `t'`, in the same order as the
original `s,t`. The equations `hs,ht` have the orientation required by `pullback.map`.
The operation equations determine the induced maps, so the theorem cannot be satisfied
by choosing unrelated operations or an unrelated map to the original arrows.

The input list retains both separatedness, both flatness, both local finite presentation
and both local quasi-finiteness assumptions. It retains the original point and finite
stabilizer fibre. The base map and its compatibility merely unpack the stated relative
groupoid, using the recorded absolute interface. The output point lies over that same
point, and its induced residue-field map is an isomorphism. An arbitrary abstract
isomorphism of the two fields would have been insufficient; none is substituted.

Finally, containment in the open implies the node's equivalent scheme equality because
pulling back an open immersion gives the restricted structure sheaf on its inverse image.
No nilpotent structure is discarded. The module and declaration docstrings identify the
source and blueprint item and the latter carries all six proof steps. The only wording
adjustment during the second pass replaced "nonreduced points" with "nonreduced fibres"
in the explanatory docstring. The statement, DAG statement and dependency records required
no correction.
