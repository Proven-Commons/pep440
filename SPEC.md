# Specification: pep440

This is the specification this library implements: the version scheme of PEP 440, local part included. Where the PEP leaves a point open, the rule this library follows is stated and marked as a choice. `packaging`, the Python library that implements PEP 440, is the reference the tests compare against; its version and the points where this library differs from it are recorded in `tests/TEST-RESULTS.md`.

## Values

A version is six parts:

- an epoch, a natural number, 0 when the text names none;
- a release, a list of natural numbers, at least one;
- an optional pre-release: one of the kinds `a`, `b`, `rc`, with a natural number;
- an optional post-release number;
- an optional dev-release number;
- an optional local part: a list of segments, where a segment is a number, or a text held as a list of characters.

A version is well formed when its release list is not empty and its local part is well formed. Every other part is a number or an optional number by construction.

An absent local part (no `+` in the text) is a different value from every local part that is there. A local part that is there is well formed when it holds at least one segment and every segment is well formed: a number segment always is, and a text segment is well formed when it is not empty, is held in lowercase letters and digits only, and holds at least one letter. The last rule is what makes it a text segment: a segment of digits only is a number segment.

## The grammar

A text is read in stages: an optional leading `v`, the epoch, the release, then the pre-release, post-release, and dev-release segments in that order, then the local part. A segment that is not there reads as absent and leaves the text untouched for the next stage. Anything left over at the end rejects the text.

### Leading v

One leading `v` or `V` may stand in front of the version and is dropped. This follows the PEP's own canonical pattern for a version, which opens with an optional `v`. The printer never writes one.

No whitespace is read anywhere: a text that starts or ends with a space, or has one inside, is rejected. Choice: `packaging` trims surrounding whitespace before it reads a version; this library does not, so the text is the version exactly as written.

### Numbers

A number is a nonempty run of digits, read as its value. PEP 440 sets no leading zero rule on any number, in the epoch, the release, or any segment: `01` reads as 1, and `1.0a01` is the version `1.0a1`. This is a place where PEP 440 differs from Semantic Versioning, which forbids leading zeros.

A separator is one of `.`, `-`, `_`.

### Epoch

Digits followed by `!` open the version: `1!1.0` has epoch 1. When the leading digits are not followed by a `!`, there is no epoch: the epoch is 0 and the digits belong to the release. A second `!` anywhere later rejects the text, since nothing else reads one.

### Release

The release is one or more numbers split by single dots: `1.0`, `2.0.1`. The release continues only while a dot is followed by a digit; a dot followed by anything else belongs to a later segment. An empty release part rejects the text: `1..1`, `1.`, and `.1` are all rejected, as is a text with no digits at all.

### Pre-release

The pre-release segment is: an optional separator, one spelling, then an optional number behind an optional separator of its own. A missing number is 0.

The spellings and the kind each one reads as, exactly as the PEP gives them:

| Spelling | Kind |
|----------|------|
| `a` | a |
| `alpha` | a |
| `b` | b |
| `beta` | b |
| `c` | rc |
| `rc` | rc |
| `pre` | rc |
| `preview` | rc |

Spellings match without case. When one spelling is the start of another, the longer one is read first: `preview` before `pre`, `alpha` before `a`. So `1.0alpha1` is `1.0a1`, and `1.0c1` is `1.0rc1`.

The optional number reads one separator when one stands there, even when no digits follow it: `1.0a.` reads as `1.0a0`. A second separator in a row is not read: `1.0a1_2` and `1.0--a1` are rejected, the first because the `_` is left over at the end, the second because no spelling follows the first `-`.

A spelling that matches nothing leaves the whole segment absent and the text untouched, separator included, for the post-release stage.

### Post-release

The post-release segment has three forms:

- the implicit form: a `-` and a number, standing right where the post stage starts, after the release or after a pre-release: `1.0-1` is `1.0.post1`, and `1.0a1-2` is `1.0a1.post2`;
- the labelled forms: an optional separator, one of the spellings `post`, `rev`, `r`, then an optional number behind an optional separator, defaulting to 0: `1.0.post1`, `1.0.r` (which is `1.0.post0`), `1.0rev2`.

The implicit form is tried first. When a `-` is not followed by a digit, the labelled reading is tried on the whole text, hyphen included, so `1.0-post` reads as `1.0.post0`. The spellings match without case, longest first: `rev` before `r`.

### Dev-release

The dev-release segment is: an optional separator, the spelling `dev`, then an optional number behind an optional separator, defaulting to 0: `1.0.dev1`, `1.0dev`, `1.0_dev4`. The spelling matches without case.

### Local part

A `+` after the dev-release stage opens the local part: one or more segments split by single separators, where a separator is a dot, a hyphen, or an underscore. A segment is a nonempty run of letters and digits. A segment of digits only reads as a number segment, read as its value, so leading zeros drop (`007` is the number 7). Any other segment reads as a text segment, lowercased, so `ABC` and `abc` are the same segment, and `foo-bar`, `foo_bar`, and `foo.bar` are the same local part.

The local grammar rejects: a `+` with nothing after it (`1.0+`), an empty segment (`1.0+a..b`, `1.0+.a`, `1.0+a.`), a second `+` (`1.0+a+b`, `1.0++a`), and any character outside letters, digits, and the three separators (`1.0+a$b`). A local part that opens with a `+` but breaks these rules is not read as an absent local part: its text is left over, and the end check rejects the whole text.

In the PEP's own grammar the local label is written with dots, hyphens, and underscores all read as separators and normalized away, which is the reading here.

### Order of the segments, and rejection

The parts come in one order: pre, then post, then dev, then the local part. A spelling out of order is left over and rejects the text: `1.0.post1a1` (a pre spelling after a post) and `1.0dev1.post1` (a post after a dev) are rejected. A pre spelling with letters after its number, such as `1.0a1b2`, is rejected the same way. Letters outside the named spellings reject the text wherever they stand, as does an empty text.

## The printer

The canonical text of a version is:

- the epoch and a `!`, only when the epoch is above 0;
- the release numbers as held, joined by dots;
- the pre-release as `.aN`, `.bN`, or `.rcN`: a dot, the kind, the number;
- the post-release as `.postN`;
- the dev-release as `.devN`;
- the local part, when it is there, as a `+` and the segments joined by dots: a number segment in plain decimal, a text segment as it is held.

Each part that is absent writes nothing. So the version spelled `1.0alpha1` prints as `1.0.a1`, `1.0-1` prints as `1.0.post1`, `v2.0RC1` prints as `2.0.rc1`, and `1.0+foo-bar` prints as `1.0+foo.bar`.

One named difference from `packaging`: the printed pre-release here carries a dot, where `packaging` prints the same value without one (`1.0a1` for what prints here as `1.0.a1`). The values are the same; the texts differ. The test results record how often this came up in the random run, with an example. A local part prints exactly as `packaging` prints it, so no difference comes from there.

## Precedence

Two versions compare by the ordering key of PEP 440, applied in this order:

1. The epochs compare as numbers.
2. The release lists compare after the shorter one is padded with zeros at the end to the length of the longer one; the padded lists then compare number by number. So `1.0` and `1.0.0` compare equal, and `1.0.1` is above both.
3. The pre-release keys compare. The key of a version is:
   - the bottom value, below every number and every kind, when the version has a dev number and no pre-release and no post-release (a dev release standing alone at its release sorts before everything there);
   - the top value, above every kind, when the version has no pre-release and is not the case above (a plain release sorts after every pre-release);
   - otherwise the kind and the number: kinds order `a` below `b` below `rc`, then the numbers compare.
4. The post-release keys compare: a missing post is the bottom value, below every post number; a present post is its number.
5. The dev-release keys compare: a missing dev is the top value, above every dev number; a present dev is its number.
6. The local parts compare. A version with no local part sorts before the same version with one. Two local parts that are there compare segment by segment:
   - a text segment sorts before a number segment. The PEP's words: when a numeric segment and a lexicographic segment are compared, the numeric segment always compares as greater;
   - two number segments compare by value;
   - two text segments compare character by character in ASCII code order over the lowercase letters and digits they are held in (the PEP compares them lexicographically and without case, which is this order once the text is held lowercase);
   - when one list is a prefix of the other, the shorter one sorts first.

The first step that decides is the answer. The key is built from an explicit three-part value (below all numbers, a number, above all numbers) for the post and dev keys, and a like value with a kind-and-number middle for the pre key, so the comparison is a plain computable function of the two versions.

The example chain printed in PEP 440, which the proofs check step by step:

`1.0.dev456` < `1.0a1` < `1.0a2.dev456` < `1.0a12.dev456` < `1.0a12` < `1.0b1.dev456` < `1.0b2` < `1.0b2.post345.dev456` < `1.0b2.post345` < `1.0rc1.dev456` < `1.0rc1` < `1.0` < `1.0.post456.dev34` < `1.0.post456` < `1.1.dev1`

## The claims

- `parse_print`: parsing the printed form of a well formed version, local part included, gives the version back. Well formed is the rule of the Values section: a nonempty release, and a local part that is absent, or holds at least one segment with every text segment nonempty, lowercase letters and digits only, and holding at least one letter.
- The chain above, step by step, proved by computation on the concrete texts, and the shorter example chain from the claim (a dev release alone below a pre-release with a dev number below the pre-release; a release below a post with a dev number below the post).
- The local ordering rules, proved the same way on concrete texts: `1.0` below `1.0+1`; `1.0+abc` below `1.0+1` and `1.0+a1` below `1.0+1` (a text segment below a number segment); `1.0+abc` below `1.0+abc.1` (the prefix rule); `1.0+1` below `1.0+2`; `1.0+abc` below `1.0+abd`.
- Equal spellings compare equal, proved the same way on concrete texts: `1.0` against `1.0.0`, `1.0a1` against `1.0.alpha1`, `1.0+ABC` against `1.0+abc`, `1.0+foo-bar` against `1.0+foo.bar`, `1.0+007` against `1.0+7`, and more in `Pep440/Proofs/Examples.lean`.
- Example valid texts print back in canonical form, local parts included, and example invalid texts are rejected, the broken local shapes among them, also proved by computation.

The comparison is not proved to be a full order in this slice: no transitivity or totality theorem is claimed. Accept and reject completeness (that the parser accepts every text the grammar allows and rejects every text it forbids) is not proved either; the tests check it against `packaging` and a strict reading of the grammar.

## The command-line tool

`Main.lean` is a small front end the tests drive. It reads one request per line and prints one answer per line. A request is an operation, then optionally one space and its input as comma-separated decimal character codes.

- `parse` takes the codes of one version text. Its answer is `ok:` and the codes of the canonical print of the parsed version, or `none` when the text is rejected.
- `cmp` takes the codes of two version texts split by one code 59, the semicolon, which cannot appear in a version text. Its answer is `lt`, `eq`, or `gt` for the precedence of the first text against the second, or `none` when either text is rejected.

A request is an operation, then optionally one space and its numbers; with no numbers after the space, the input is empty. A malformed request prints `error`: any other line, an unknown operation, a number that is not plain decimal digits, a character code that is not a Unicode scalar value, or a `cmp` request with no semicolon code in it. A line may end in LF or CR LF; nothing else around a request is ignored.
