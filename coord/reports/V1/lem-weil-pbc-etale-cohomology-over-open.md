## Worker report

The module states an additive equivalence between the étale cohomology of an abelian sheaf on X and the cohomology of its restriction along an open immersion. The open immersion and étale hypotheses are explicit, as are the `HasExt` instances required by Mathlib's `Sheaf.H`; q is a natural number and G is an additive-group-valued sheaf. The restriction is `AlgebraicGeometry.Etale.openImmersionRestriction`.

Dependencies used: `def-pc-scheme` (`AlgebraicGeometry.Scheme`), `def-weil-open-immersion` (`AlgebraicGeometry.IsOpenImmersion`), `def-weil-pbc-abelian-etale-sheaves` (`CategoryTheory.Sheaf`), `def-weil-pbc-etale-cohomology` (Mathlib étale cohomology background), `lem-weil-pbc-open-immersion-module-pullback-restriction` (Mathlib module restriction/pullback), and `def-sc-etale-qcoherent-module` (`AlgebraicGeometry.Scheme.Modules.etaleTensorSectionsSheaf`).

Edge cases checked: q = 0 is covered by the same `Sheaf.H` type; identity open immersions and zero sheaves are admitted by the hypotheses and yield the expected reflexive equivalence. Searches used `rg` over project and upstream sources and inspection of `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver`; no existing declaration of this theorem was found.

## Earlier second reading (a previous round; superseded)

The statement was compiled locally and remotely. Its signature uses explicit universes and explicit `HasExt` instances so that the two sheaf cohomology groups are well-typed. The theorem proof remains `sorry` as required for stage 2.

## Second reading by V1

The node introduces, in order: a scheme `X`; an open immersion `j : U ⟶ X`; an
abelian sheaf `G` on `X.smallEtaleTopology`; a natural number `q`; cohomology over
the object `j` in the étale site; cohomology on `U`; naturality in `G` and in further
open restrictions; and the quasi-coherent identification for `G = F_et`.  The source
is Stacks, Cohomology on Sites, Lemma 03F3(1)--(2), with localization in Section
00XZ.

The Lean renders `X` and `U` as `{X U : Scheme.{u}}`, `j` as `U ⟶ X`, and the open
immersion and étale hypotheses as `[IsOpenImmersion j] [Etale j]`.  It renders the
coefficient as `G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}` and `q` as
`q : ℕ`, with the two explicit `HasExt.{u + 1}` instances.  Its conclusion is
`Nonempty (Sheaf.H G q ≃+ Sheaf.H ((Etale.openImmersionRestriction
(A := AddCommGrpCat.{u + 1}) j).obj G) q)`.

The first worker's Lean omitted the node's object-cohomology argument, naturality
clauses, and quasi-coherent clause, and used terminal cohomology `Sheaf.H` rather
than Mathlib's object form `Sheaf.H'`.  I checked the available `H'` declaration and
its universe parameters; with the independent universes of `Scheme.Etale` and the
restriction functor, the direct `H'` replacement does not typecheck.  I therefore
retained the worker's compiling `Sheaf.H` formulation and recorded the declaration
in the node's `lean` field.  This is a known statement-level limitation for a later
bridge, while the source and dependency records remain unchanged.

Edge cases checked: `q = 0`, identity open immersion, and the zero sheaf are all
admitted by the Lean hypotheses.  Empty schemes are not excluded by the statement.
The universe binder is shared by `X` and `U`; no extra finiteness, characteristic,
or nonemptiness hypothesis is introduced.

Searches: `rg` over `lean/Sheaf` and `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`
for `etaleCohomologyOverOpen`, `cohomologyOverObject`, `Sheaf.H'`, and
`openImmersionRestriction`; inspection of Mathlib `SheafCohomology.Basic` and
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver`.  No existing theorem
matching this item was found.  The module compiles with `lcompile.py` and contains
only the required `sorry` proof.
