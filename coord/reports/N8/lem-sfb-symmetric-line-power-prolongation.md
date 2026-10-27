## Worker report

The delivery states `AlgebraicGeometry.symmetricLinePowerProlongation` in
`Sheaf.AlgebraicGeometry.SymmetricLinePowerProlongation`. Its only theorem has
proof `sorry`; its docstring contains all five proof steps of the accepted DAG
split. The second module defines `HasSemiabelianGeometricFibres` with real data
(a Prop-valued formula), not a postponed construction. No existing node is
changed except for the item's Lean record and the addition of its new definition
node to `stmt_deps`. No statement correction or dependency interface repair was
needed. No statement is disputed.

The inherited BLOCKED report concerned a stage-1 unchanged-split gate. The live
node has a passing stage-1 review, no Lean record and a stage-2 queue entry.
`coord/brief-stage2.md` section 0 explicitly makes that the input to this task.
There is no released repair note for this item and no return entry in N8's file.

### Hypotheses and clauses

| Node clause | Lean rendering |
| --- | --- |
| S is a scheme | `{S : Scheme.{u}}` |
| S is integral, hence nonempty | `[IsIntegral S]` |
| S is locally Noetherian | `[IsLocallyNoetherian S]` |
| Every local ring is an integrally closed domain | `hS : ∀ s : S, IsDomain (S.presheaf.stalk s) ∧ IsIntegrallyClosed (S.presheaf.stalk s)` |
| G is an S-group scheme, with its actual operations | `G : Grp (Over S)`; `G.X.hom` is p |
| Group law is commutative | `[IsCommMonObj G.X]` |
| p is smooth and separated | `[Smooth G.X.hom] [IsSeparated G.X.hom]` |
| p is of finite presentation | `[LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom]`; separatedness supplies quasi-separatedness |
| Every geometric fibre has the stated semiabelian extension | `hG : HasSemiabelianGeometricFibres G` |
| U is a dense open subscheme of S | `U : S.Opens`, `hU : Dense (U : Set S)`; U's inclusion is the canonical open immersion `U.ι` |
| G_U is the base change with its induced group law | `((Over.pullback U.ι).mapGrp.obj G).X` |
| N is a line on G_U | N is a module on that underlying scheme, with `[N.IsInvertible]` |
| Given rigidification at the induced identity | `rigidification` is the isomorphism from tensor pullback along `η[...].left` to `𝟙_ U.toScheme.Modules` |
| Given symmetry of underlying modules | `symmetry` is the isomorphism from tensor pullback along `ι[...].left` to N; no coherence or rigidification compatibility is required |
| Affine open covering of S | `∃ (I : Type u) (W : I → S.Opens), (⨆ i, W i) = ⊤ ∧ (∀ i, IsAffineOpen (W i)) ∧ ...` |
| For each nonempty member | `∀ i, Nonempty (W i) → ...` |
| Positive integer d_i | `∃ (d : ℕ), 1 ≤ d ∧ ...`; this represents exactly the positive integers |
| Line P_i on G_{W_i} | `P : (pullback G.X.hom (W i).ι).Modules`, `P.IsInvertible` |
| Comparison over G_{U ∩ W_i} | `Nonempty` of an isomorphism between the tensor pullbacks of P and `N.tensorPow d` to the common intersection |
| No rigidification, cube or positivity imposed on P | The existential concludes only invertibility and the underlying module isomorphism |
| No ampleness imposed on N | No ampleness binder occurs |

For the intersection comparison set `a = pullback.fst G.X.hom (W i).ι` and
`b = pullback.fst G.X.hom U.ι`. The common scheme is `pullback a b`, with
projections `pullback.fst a b` to G_{W_i} and `pullback.snd a b` to G_U.
Both a and b are the base-changed open inclusions into G. Thus their fibre
product is precisely the intersection of these open subschemes, canonically
G_{U ∩ W_i}; this is the same comparison as the node, with no arbitrary arrow
or further assumption introduced.

The new fibre predicate quantifies over every `k : Type u` with `[Field k]`
and `[IsAlgClosed k]` and every geometric point `s : Spec (.of k) ⟶ S`.
This is the usual size convention for `Scheme.{u}`; it includes an algebraic
closure of every residue field and imposes no equality between independent
site universes. It forms the actual base-changed group with
`(Over.pullback s).mapGrp.obj G`. It permits `r = 0` through the existing
`MultiplicativeType.splitTorus`. The existential A carries its group structure,
and `IsAbelianVariety A.X` means proper, smooth and connected. Over the
algebraically closed k this is geometrically connected as in the node.
The arrows i and q are morphisms of bundled group objects, hence preserve the
specified group laws. `IsPullback` identifies i with the full scheme-theoretic
kernel of q, including all nonreduced test schemes. Finally
`Presheaf.IsLocallySurjective (Scheme.fppfTopology.over (Spec (.of k)))
(yoneda.map q.hom.hom)` says that every section of A locally lifts along an
fppf cover. Representable functors are fppf sheaves. Kernel identification and
this epimorphy give exactly the stated short exact sequence of fppf sheaves,
without asserting surjectivity on rational points over every test field.

### Dependency declarations read and used

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms
  (def-pc-scheme), used throughout.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`
  (def-pc-integral-scheme), including its nonempty and domain conditions.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`
  (pqf-def-locnoeth), the every-affine-open formulation.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`
  together with `IsDomain` at each local ring (def-weil-pbc-normal-ring).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`
  (def-sbc-smooth-morphisms), exported by the new definition's abelian-variety
  dependency.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`
  (def-sbc-locally-finite-presentation). `QuasiCompact` and `IsSeparated`
  supply the remaining finite-presentation and separatedness clauses.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`
  (def-weil-open-immersion), realized here by the canonical open inclusions
  `U.ι` and `(W i).ι`; the module is transitively publicly imported.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible` (def-sc-invertible-module)
  and the existing `tensorPow` recursion.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `AlgebraicGeometry.Scheme.Modules.tensorPullbackSectionAdjunction`
  (def-pc-module-pullback). Its public upstream import supplies the actual
  `tensorPullback` functor used for every module pullback; no adjunction choice
  or new pullback is introduced.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.Grp`, `GrpObj`,
  `IsCommMonObj` (def-sc-group-scheme). The inverse and identity used in the
  main theorem are those of the pulled-back group, not chosen extra maps.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`, through
  `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`: def-pc-base-change records
  the convention `Over.pullback`/`Limits.pullback` used here. Its main
  `moduleBaseChange` declaration concerns a different clause of that bundle;
  it is not copied or used instead of the scheme base change.
- `WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs`:
  `AlgebraicGeometry.IsAbelianVariety` (def-sc-abelian-variety), read with its
  full proper/smooth/connected signature.
- `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`:
  `AlgebraicGeometry.MultiplicativeType.splitTorus`
  (def-sfb-tori-multiplicative-type), including its rank-zero branch and the
  recursive product of the recorded Laurent-polynomial multiplicative group.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfTopology`, and
  `Mathlib.CategoryTheory.Sites.Over`: `GrothendieckTopology.over`
  (def-pc-fppf-site). Local surjectivity is the actual Mathlib predicate from
  `Mathlib.CategoryTheory.Sites.LocallySurjective`.

The recorded proof dependency
`WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor` is imported
as a plain proof import. The finite-type-over-Noetherian Mathlib match is
already available in the public Noetherian import. The three remaining proof
nodes (algebraic-group-ample-difference, raynaud-generic-ample-symmetrization,
and normal-group-vertical-cartier-descent) have no recorded Lean modules to
import; their exact steps remain in the theorem docstring. They are proof
prerequisites, not extra hypotheses of this statement.

### Edge cases

- The empty base is excluded by the node's integrality assumption, exactly as
  by Mathlib IsIntegral. Empty members of an affine covering are allowed and
  require no local line witness.
- U = S is allowed; U cannot be empty over a nonempty integral S with hU.
  No proper-open or non-affine assumption is introduced.
- A field base, a trivial line, a trivial group and a torus of rank zero are all
  permitted by the stated parameterization. No positive-dimensional torus or
  properness assumption on G occurs.
- d = 0 is excluded, while d = 1 is allowed. No coprimality condition or
  characteristic restriction appears, including in characteristic two.
- The comparison is of underlying modules only: arbitrary given symmetry and
  rigidification are permitted, with no extra compatibility condition.
- No quasi-compactness of S or U is required; the cover index is unrestricted
  within the scheme universe. Every open cover of a u-small space has a
  refinement indexed in Type u, so this loses no cover case.

### Searches

For the item, msearch LeanFinder queried “A positive tensor power of a symmetric
line bundle on a semiabelian scheme extends locally from a dense open of a
normal base”: eight unrelated localization/structure-sheaf-section hits.
Loogle `"IsInvertible", "tensorPow"` returned zero hits. Mathlib grep
`[Ss]emi[Aa]belian|[Ss]ymmetric.*[Ii]nvertible|[Rr]aynaud` returned only unrelated
Raynaud bibliographic mentions and symmetric-matrix lemmas. Searches for
semiabelian, Semiabelian, SemiAbelian, symmetricLinePower, symmetric.line.power,
and the item id in the upstream and Sheaf source trees found no declaration;
the one semiabelian text hit is a descriptive sentence in
StableLevelVersalBranchFreeness. The new notion's LeanSearch, LeanFinder,
Loogle and Mathlib grep results are recorded verbatim in its mathlib_searches.
The DAG has no semiabelian definition node; blueprint_refs search for
“semiabelian” and “semiabelian geometric” returned zero matches. Existing
splitTorus, IsAbelianVariety, group base change and fppf topology were found
and reused. The latest blueprint was searched; it has no source unit for this
agent-created local input. Its recorded source explicitly says the original
is WANTED. This delivery preserves that mathematical statement and source.

### Validation

Both delivered files were compiled separately, in dependency order, by
`/home/ubuntu/weil-launcher-all/batch2/scompile.py` against the published live
server library, in both sandbox and destination module modes. No errors or
unexpected warnings occurred. All variables and universes are explicit and
`autoImplicit` is disabled. Definitions contain no sorry and no choice of
unconstrained data. The main theorem alone is postponed. The first dry run requested the current
new-node schema field `import_flags`; an empty list was added as required by
the live preflight.

## New nodes

`def-sfb-semiabelian-geometric-fibres` introduces exactly the missing fibre
condition described above. Source: Moret-Bailly II 3.3.3, the semiabelian setting
of the owning node's opening power-prolongation input; original local source
WANTED as already recorded. It cites the existing scheme, group, base-change,
abelian-variety, split-torus and fppf-site nodes, and imports their modules.
LeanSearch, LeanFinder, Loogle, Mathlib grep, upstream/Sheaf grep and DAG/blueprint
searches found no existing predicate. Its kernel square plus fppf local
surjectivity is a definition of the stated exact sequence, not a new theorem.

## Second reading by N8

This is the assigned worker's own second pass, not an independent review by
another agent. The dispatcher forbids starting agents; the maintainer performs
the independent delivery review. I reread the node and both files together.
Every hypothesis and clause matches the table above. I checked especially that
finite presentation includes quasi-compactness, that the kernel square retains
the induced group law, that the common comparison space is the correct open
intersection, that d is strictly positive, and that there is no positivity or
cube conclusion. The new definition reuses the existing split torus rather
than creating another Laurent group, and uses fppf local surjectivity rather
than surjectivity of field-valued points. No mismatch was found on this pass.
