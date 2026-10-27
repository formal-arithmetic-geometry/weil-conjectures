## Worker report

The module `Sheaf.AlgebraicGeometry.FppfCoproductEqualityLocus` states
`AlgebraicGeometry.Scheme.fppfSheaf_coproduct_equality_locus`. Its proof is `sorry`.
The two definitions contain real data: `fppfEqualityOpenInclusion` uses the existing
restriction functor followed by `Over.map`, and `fppfEqualityCoproductProjection`
is the colimit descent of the maps through the intersection opens. They are helpers
of this node's canonical comparison, not separate notions or independent results.
Every declaration has a source and blueprint docstring; the theorem includes all
five natural-language proof steps of the DAG node.

The source was read in `literature/stacks-project/spaces.tex`: Tag 02WQ,
`lemma-coproduct-algebraic-spaces`, explicitly omits the diagonal verification;
Tags 0F15 (`lemma-coproduct-sheaves-open-and-closed`) and 02WO
(`lemma-representable-sheaf-coproduct-sheaves`) supply the clopen summand geometry.
The present theorem is precisely the extracted verification described by the node.
The node's statement and proof are unchanged.

Hypotheses and clauses, in order:

- The base scheme is `S : Scheme.{u}`. Site objects and S-morphisms are `Over S`.
  The big fppf topology is Mathlib's `fppfTopology.over S`.
- The size convention is explicit `universe u v`; `I : Type (max u v)` and the
  coefficient category `Type (max u v)` include the scheme morphism universe.
  There is no finite, inhabited, or equality-of-universes assumption. Lifted
  representables `uliftYoneda.{v}` put Hom sets into this same coefficient universe.
- The arbitrary sheaves of sets are the family `G`; the chosen sheaf coproduct is
  `C`, with coprojections `c` and its universal property `hc : IsColimit (Cofan.mk C c)`.
  This quantifies over every coproduct presentation, without imposing a global
  sheafification instance or a stronger assumption on the summands.
- The test object is `T : Over S`; `a b : C.obj.obj (op T)` are the two sections.
- `A B : FppfCoproductPartition G T` are the existing partition records, now owned by
  `def-trf-fppf-coproduct-partition-data`: their
  `opens`, `isClosed`, `disjoint`, and `covers` fields are exactly the clopen
  partitions, and their `sections` fields are the component sections.
  `hA : A.MapsTo c a` and `hB : B.MapsTo c b` are exactly the two component-image
  equalities from the node. Empty open pieces are allowed by these records.
- The same-label intersections D_i are the literal lattice intersections
  `A.opens i ⊓ B.opens i`. Their open subscheme structures are
  `fppfPartitionOpen T (A.opens i ⊓ B.opens i)`.
  The restrictions of component sections are the maps of `G i` along
  `fppfEqualityOpenInclusion T inf_le_left` and its `inf_le_right` version.
  Their domains are inferred to be that intersection from the declared type of `p`.
- `E : I → Over S` supplies the representing schemes; `p i` is their map to D_i.
  Each `hE i` is the cartesian square with top-left h_(E_i), bottom-left h_(D_i),
  top-right G_i, and bottom-right G_i × G_i. The right arrow is
  `prod.lift (𝟙 (G i).obj) (𝟙 (G i).obj)`, the diagonal, and the bottom arrow
  is the pair of the restricted component sections under `uliftYonedaEquiv.symm`.
  The top arrow is explicitly the first restricted component section pulled back
  along `p i`. The commutativity field is its equality with the second section.
  The pullback universal property says exactly that maps to E_i over a map to D_i
  correspond bijectively to equality of those component pullbacks. It is equivalent
  to the node's representability hypothesis on schemes over D_i: arbitrary maps
  from Z over S to D_i are precisely the objects over D_i being tested.
- `L : Over S`, coprojections `j`, and `hL : IsColimit (Cofan.mk L j)` specify
  the chosen coproduct of E_i, by its universal property. Coproducts in this slice
  are the underlying scheme coproducts with their induced map to S; the forgetful
  functor preserves colimits. Thus these are the data of the coproduct named in
  the node, rather than an additional geometric restriction. This presentation
  also avoids an extra `Small.{u} I` assumption: only the specified coproduct needs
  to lie in the chosen site, as the node's size convention already requires.
- Write q for `fppfEqualityCoproductProjection T (fun i ↦ A.opens i ⊓ B.opens i)
  E p L j hL`. Its definition is `hL.desc` applied to the cofan with components
  `p i ≫ fppfPartitionInclusion T (A.opens i ⊓ B.opens i)`, exactly the induced map
  from the node. No unconstrained map has replaced this canonical construction.
- The conclusion is `IsPullback` with top-left h_L, top-right C, bottom-left h_T,
  bottom-right C × C. The left arrow is `uliftYoneda.map q`, the right arrow is
  the diagonal, the bottom arrow is the pair of sections a,b, and the top arrow
  is the section a pulled back along q. This is the node's explicitly equivalent
  conclusion `h_E ≃ h_T ×_(C × C) C`, with its specified projection.
- In a presheaf category the pullback universal property is pointwise and natural.
  A point on the bottom-right constraint is `(f,s)` with `(f*a,f*b)=(s,s)`;
  eliminating the uniquely determined s gives exactly
  `Mor_S(Z,L) ≃ {f : Z ⟶ T | C.obj.map f.op a = C.obj.map f.op b}`.
  The projection is composition with q, by the displayed left arrow. This
  establishes every bijection/naturality/projection clause in the node, rather
  than only nonempty representability or an unspecified object isomorphism.
- On E_i, the descent equation gives `j i ≫ q = p i ≫ inclusion(D_i,T)`.
  Naturality of c_i and hA/hB identify the restrictions with the component
  sections, and the commutativity of hE i is their specified equality. Hence the
  global comparison restricts to exactly the given local comparison; there is no
  independent choice of a comparison on the summands. Equality witnesses are
  propositions, so this also preserves their unique proof data.
- No `IsAlgebraicSpace`, representable-diagonal, atlas, separatedness, flatness,
  or finiteness hypothesis is imposed on G_i.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its `Hom` and `Opens`.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage`, `Scheme.fppfTopology`;
  `Mathlib.CategoryTheory.Sites.Over`: `GrothendieckTopology.over`.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`: the site convention
  `Precoverage.IsSiteForCoverings` was read. The sheaf-of-sets part of that node
  uses Mathlib `Sheaf` directly, as its record directs; its covering-axiom
  predicate need not be restated or added as a premise for the fixed fppf site.
- `Mathlib.CategoryTheory.Limits.HasLimits` and `Shapes.Products`: `colimit`,
  `IsColimit`, `Cofan.mk`, and `IsColimit.desc` give the coproduct universal
  properties. Both colimit hypotheses describe chosen objects already named
  in the node, and do not replace a missing mathematical hypothesis.
- `Mathlib.AlgebraicGeometry.OpenImmersion` and `Restrict`: `IsOpenImmersion`,
  `Scheme.restrictFunctor`, `Scheme.homOfLE`. `CategoryTheory.Over.map` transports
  the existing open inclusions to the base S; no second open-subscheme construction.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: the signature and docstrings of
  `AlgebraicSpace.IsRepresentableWith` and `IsRepresentable` were read. They encode
  scheme-test representability by the same actual `IsPullback` squares used here.
  No algebraic-space assumption is needed. We use `IsPullback` directly for the
  specified representing object, and `uliftYoneda` for the allowed larger coefficient
  universe, rather than the Type-u-only global map predicate.
- `Sheaf.AlgebraicGeometry.FppfSheafCoproductPartition`:
  `Scheme.fppfPartitionOpen`, `fppfPartitionInclusion`, `FppfCoproductPartition`,
  `FppfCoproductPartition.MapsTo`, and proof dependency
  `Scheme.fppfSheaf_coproduct_partition`. The data and predicate are now owned by
  `def-trf-fppf-coproduct-partition-data`, which is added to stmt_deps; the theorem
  `lem-trf-fppf-sheaf-coproduct-partition` stays exclusively in proof_deps.
- `Mathlib.AlgebraicGeometry.Limits`: the scheme coproduct instance,
  `sigmaOpenCover`, `disjoint_opensRange_sigmaι` were read for the family-coproduct
  dependency. This is a statement dependency and the geometric proof ingredient.
- `Mathlib.AlgebraicGeometry.Gluing`: `Scheme.Cover.glueMorphisms`,
  `ι_glueMorphisms`, and `hom_ext` were read; this is a plain proof-only import.
- `Mathlib.CategoryTheory.Yoneda`: `uliftYoneda`, `uliftYonedaEquiv`;
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs`: `IsPullback`;
  `Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts`: `prod.lift`.

Edge cases checked before writing: I empty forces T empty through the two partition
cover fields and L empty through its coproduct property. Representable presheaves
then give the required singleton on an empty test scheme and no maps on a nonempty
one. Empty pieces and empty intersections remain schemes and are not excluded;
the local representing square forces their equality schemes empty. For one index
the statement reduces to the given equality representation. Different A and B
partitions are permitted; only their same-label intersections enter E. Infinite
families and nonreduced test schemes are permitted. No connectedness, reducedness,
or nonemptiness assumption was introduced. Higher coefficient and index universes
are explicitly supported, with the chosen coproduct in the site specified by hL.

Searches for an existing statement (2026-10-22):

- `msearch.py leanfinder`: "The equality locus of two sections of a coproduct of
  fppf sheaves is represented by the coproduct of the component equality schemes".
  Eight results: topological ring-sheaf `objSupIsoProdEqLocus` and its inverse lemma,
  scheme `isEmpty_pullback_sigmaι_of_ne`, `isEmpty_of_commSq_sigmaι_of_ne`,
  `sigmaι_eq_iff`, `coprodPresheafObjIso`, an affine-transition Hom lemma, and
  `LocalRepresentability.glueData_V`. None states the fppf equality comparison.
- `msearch.py loogle`: "CategoryTheory.Sheaf, CategoryTheory.Limits.IsPullback".
  Zero hits; the service reports the latter qualified identifier unknown (the
  actual declaration is `CategoryTheory.IsPullback`, read from source).
- `msearch.py leansearch`: "Equality locus of sections of a coproduct of fppf
  sheaves is represented by a coproduct of schemes". Eight results: coproducts
  of locally ringed spaces, scheme finite coproducts and monomorphisms, coproducts
  of affine spectra, `coprodPresheafObjIso`, affine descent maps, scheme disjoint
  coproducts, and affine finite coproducts. None is the desired comparison.
- `msearch.py grep`: `coproduct.*equaliz|equaliz.*coproduct|coproduct.*equality|equality.*coproduct`.
  Results concern categorical coproduct/coequalizer constructions and locally ringed
  space colimits. None concerns equality loci of sections of fppf sheaves.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for equality-locus names,
  `coproduct.*equal`, `equal.*coproduct`, `fppf.*[Ee]quality`, and the reverse pattern:
  no existing statement; the algebraic-space coproduct module only mentions the
  argument in its docstring. The existing partition module was reused, not copied.
- An explicit search of `lean/WeilConjectures` for this blueprint id had no hit.
  Searches of both source roots and `dag/lean_names_upstream.json` for all three
  proposed declaration names had no hit. The return identifies a missing DAG definition owner: the new node below
  records these exact existing project data with `existing: true`.

Validation: `scompile.py Q75 lem-trf-coproduct-equality-locus` compiled the delivered
module in sandbox and library-module modes, each separately within 60 seconds,
with no errors and no unexpected warnings. The initial noncomputability diagnostic
for the restriction functor was repaired by declaring its helper noncomputable;
its data remain the actual functor map. No statement correction or dispute.

## New nodes

`def-trf-fppf-coproduct-partition-data` owns the existing declarations
`fppfPartitionOpen`, `fppfPartitionInclusion`, `FppfCoproductPartition`, and
`FppfCoproductPartition.MapsTo` in
`Sheaf.AlgebraicGeometry.FppfSheafCoproductPartition`, via `existing: true`.
Its self-contained definition is the clopen partition with component sections and
the predicate that those sections map to a given section. Source: Spaces 0F15,
its proof constructing the clopen pieces, and 02WO for arbitrary families.
The module was read both locally and from live server source (`scompile.py --source`);
the declarations agree. No new Lean module and no duplicate definition are needed.
The partition theorem remains a proof dependency of the equality-locus item;
its existence and uniqueness assertions are not used as definitions.

New-node searches, run during this repair: LeanSearch query "Clopen partition of a
scheme with a section in each fppf summand sheaf and a predicate that component
sections map to a given section" returned eight results, including `IsClopen`,
`isClopen_range_sigmaMk` and `coprodPresheafObjIso`; none is this data record.
LeanFinder query "A clopen partition of a scheme with a section in each summand
fppf sheaf and component sections mapping to one given section" returned eight
results about zero sections, open covers and gluing, with no exact match.
Mathlib grep `FppfCoproductPartition|fppfPartitionOpen|fppfPartitionInclusion|fppf.*[Pp]artition`
returned zero hits. Source grep found no upstream definition and precisely the
published Sheaf module above. DAG grep found only theorem nodes using or carrying
these declarations, with no definition owner; `blueprint_refs.py search
FppfCoproductPartition` returned zero blueprint matches. The new node stores the
actual search-log results. This directly repairs H2 of head `1cc2afb8afe6`.

## Second reading by Q75

Author's second reading, performed with the live DAG item, saved Lean module,
existing partition module, new definition node and Spaces 0F15/02WO/02WQ open.
This is a fresh self-check, not an independent agent review: the dispatcher forbids
starting other agents. The maintainer supplies the independent review.

I checked `S`, `I` and `G` against the first sentence: `Over S`,
`fppfTopology.over S` and `Type (max u v)` retain the site and size convention.
`C`, `c`, `hc` state precisely a chosen sheaf coproduct; `T`, `a`, `b` are the
test scheme and its two sections. I read the five fields of the existing
`FppfCoproductPartition`: `opens`, `isClosed`, `disjoint`, `covers`, `sections`.
They give exactly the two clopen partitions with component sections. I unfolded
`MapsTo`: the equation is the image under `c i` equal to the restriction along
the actual open inclusion, exactly the two component-image hypotheses.
The new definition node spells out these same fields and predicate, including
empty pieces, without asserting the partition theorem's existence or uniqueness.

For `D_i`, both occurrences in the Lean use `A.opens i ⊓ B.opens i`;
the two `fppfEqualityOpenInclusion` maps are respectively `inf_le_left` and
`inf_le_right`, so they restrict the correct component sections. In `hE i`,
the left arrow is the specified `p i`, the right arrow is the diagonal of `G i`,
and the bottom arrow pairs those restrictions. The top arrow is their first
restriction along `p i`, so the commutative square states the given local equality.
Its pullback property is exactly the local representing property.

`L`, `j`, `hL` specify the scheme coproduct over S. The definition of
`fppfEqualityCoproductProjection` is `hL.desc` on `p i` followed by the inclusion
of `D_i` into `T`; it supplies the specified induced map. In the conclusion the
left arrow is its lifted Yoneda map, the bottom arrow pairs `a` and `b`, and the
right arrow is the diagonal of `C`. Thus its pullback property is precisely the
stated natural equality-locus bijection, with its projection; the top arrow is
`a` restricted along the induced map, ensuring the stated local compatibility.
No algebraic-space, finite-index or nonempty-index assumption was added.
I rechecked empty `I`, empty intersections, unequal partitions, one index and
infinite `I`: none is excluded and the local and global representing properties
reduce as described in the edge-case check above.

The only mismatch found was DAG ownership: the saved packet cited the partition
**theorem** as a statement dependency for plain definition data. The item now
cites the new definition owner instead, while retaining the theorem as a proof
dependency. The item's mathematical statement, proof and Lean signature did not
change. This paragraph and the checks above replace the former H11 placeholder.
