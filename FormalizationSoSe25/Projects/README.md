## Personal Info

Please fill out the following. You can fill in the project topic once you have decided.
```
Name: Jonas Harder
Project topic: Coarse Equivalence of R^n and Z^n
```

## Your own project

During the second half of the course you will work on a project in any area of mathematics of your choice. You can put your project files in this folder.

Since a project likely consists of more than 1 file, it will be useful to publish this as a repository on GitHub.

## Git Instructions

We will be using git via the interface on VSCode. You can also do it from the command line.

### Getting started

* Create an account on `github.com`
* On the command line, run the following two commands, with your name and email substituted in: (you can open a terminal in VSCode with `ctrl+J`/`cmd+J` and clicking `Terminal`)
```
git config --global user.name "Your Name"
git config --global user.email "youremail@yourdomain.com"
```
* In VSCode, open this file and add your name at the top.
* Save all your open files
* Click on the `Source Control` button (left bar, third button from the top).
* Write a small commit message (what you write is not important, but it should not be empty). Press `Commit`.
* Press `Yes` (or `Always`) on the prompt `There are no staged changes to commit. Would you like to stage all changes and commit them directly?`. This will also commit your changes to all other files, which is fine.
* Press `Sync changes`
* Press `OK` (or `OK, don't show again`) when prompted `This action will pull and push commits from and to "origin/master"`
* In the new window, press `Sign in with browser`
* If needed, sign in to GitHub
* Press `Authorize git-ecosystem`
* You get the message that you don't have permission to push. Press `Create Fork`.
* You should now see your changes at `github.com/<YourGitHubUsername>/FormalizationSoSe25`.

### Pushing Later Commits

Pushing another commit after the first one is easy:

* Save all your open files
* Write a small commit message and press `Commit`.
* Press `Sync changes`

Make sure to commit your work at least occasionally (and definitely before giving the presentation). Committing early and often can help keep me updated on your status.

### Pulling commits

After you create your fork I believe that VSCode will not `sync` or `pull` new changes correctly by itself anymore, since it will pull from your fork by default.

To get new changes, do the following:
* Press the three dots icon at the top-right of the `source control` panel `... > Pull / Push > Pull from ... > upstream/master`
* (optionally) press `sync changes`.

Note: After you have created a fork, `git pull` will likely not work anymore from the command line. You can still pull changes from the command line using `git pull upstream master`.

### Command-line

If you would like to use Git from your command-line instead, you can use the commands `git pull`, `git add`, `git commit -am "commit message"`, `git push`, `git status`, `git log`, among others. Google for information how to exactly use these commands.

## Formalization Tips

Here are some tips for your project.

### Read relevant mathlib files

* There is a rough Mathlib overview here: https://leanprover-community.github.io/mathlib-overview.html
  This can give you an idea what is already in Mathlib.
* Make sure you look through Mathlib what related concepts to your project already exists. It is useful to use https://leansearch.net/ for this
* Look at the related work in more detail in the Mathlib docs:
  https://leanprover-community.github.io/mathlib4_docs/.
  For some results, opening the file in Lean will give you even more information.
* The link above is for the newest version of Mathlib. It is possible that some things have changed slightly since the course started. There is also a version of the documentation pages for the exact version of Mathlib this course uses, here: https://florisvandoorn.com/LeanCourse24/docs/
* Step through some of the proofs in Lean.
  You can open the file locally by going to e.g.
  `FormalizationSoSe25/.lake/packages/mathlib/Mathlib/Algebra/Group/Basic.lean`
  Note that the `.lake` folder is hidden in VSCode sidebar, but you can navigate through it with `ctrl+O` or `cmd+O`.

### Searching

During class I already discussed searching using the name (using autocomplete or the mathlib docs), or the statement (using `apply?` or `rw?`). Additional options:

* Search Mathlib using natural language: https://leansearch.net/
* Search Mathlib using precise syntax: https://loogle.lean-lang.org/
* Searching on GitHub directly: https://github.com/leanprover-community/mathlib4
  - This can be useful when searching for a mathematical theorems using its name,
    since the mathlib docs search doesn't search through the documentation of a definition or theorem (only its name).

### Asking for help

* If you have trouble with anything, make sure to ask me or other students for help during class or office hours.
* If you are stuck on something, try replacing it by `sorry` and move on to the next part until you can ask about it.
* You are allowed to ask any AI for help. I do not necessarily recommend using them, often their suggestions are not very helpful.
  * GitHub copilot can sometimes help with stating lemmas or proving a set.
  * ChatGPT knows some Lean, but it bad at proofs and often suggests outdated Lean 3 syntax

### Writing definitions

It is useful to find a definition that already exists in mathlib and is similar to what you want.
Then you can mimic the structure of that definition.
This can also be useful in deciding whether to use `def`, `structure` or `class`.

## Presentations

At the end of the semester, you should give a presentation on your project during class.
The presentation should be 20-25 minutes, plus 5 minutes for questions.

During your presentation, you can discuss the following (but you don't have to treat every point)
* Explain the mathematical content of your formalization
* Show some of the formalized work (for example if you have found interesting way to state a definition, or the statement of the theorem you proved).
* What went easily when formalizing? What was hard? Were any tools or tactics particularly useful, or did you miss a specific tactic?

You do not have to finish your project before your presentation, so your presentation is probably about the ongoing work.

## Handing in your project

Projects are due at the end of the semester (precise date forthcoming).
To "hand-in" your project, you just have to push to your fork of GitHub, and check that all the files show up on GitHub.

Your project should contain a short description of it contents, to help judge what you've formalized. This should be included in the repository as a pdf or markdown file (not Word or rich text format).

Please answer the following questions:

* What are the main results in your formalization.
* Do you have any `sorry`'s or unfinished proofs? Describe what part (if any) is unfinished.
* What references/sources have you used?

## Acknowledgement
This file is modeled based on work of [Floris van Doorn](https://florisvandoorn.com/) for his [course in Winter semester 2024](https://github.com/fpvandoorn/LeanCourse24/).