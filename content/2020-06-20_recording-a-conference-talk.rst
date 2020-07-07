=======================================================
 Recording and editing a talk for an online conference
=======================================================

:tags: talks
:category: Tools
:authors: Clément Pit-Claudel
:summary: A step-by-step guide on using ``guvcview``, ``ffmpeg``, and ``aegisub`` to assemble a talk video.

.. preview::

   Most PL conferences moved online this year, and many are asking authors to pre-record talks to avoid livestreaming difficulties.  Here are the steps we followed to record and edit our `Kôika talk <https://www.youtube.com/watch?v=5W9v-n-EZuo>`_ at PLDI 2020 and our `extraction talk <https://youtu.be/CQHoQRBD5Xk?t=3738>`_ at IJCAR 2020.  This posts covers preparing and recording the talk, adding the slides, and captioning the final video.

Many people at PLDI swore by `OBS studio <https://obsproject.com/>`_, though, so you should check that out too.  My colleague Jason Gross also points out that Zoom has an `automatic captioning feature <https://support.zoom.us/hc/en-us/articles/115004794983-Automatically-Transcribe-Cloud-Recordings->`_ for paid plans, so if you're confident recording everything at once and you have Zoom you can create a private room and use that feature.

Step 1: Make the slides
=======================

The exact format doesn't matter too much, since you'll record a video of your screen flipping through the slide deck anyway.  We used Google Slides to facilitate remote collaboration (my favorite is usually `beamer <https://people.csail.mit.edu/cpitcla/links/2016-07-21-CAV-triggers.pdf>`_).  For some reason it will sometimes switch the background color of all the liner notes to dark grey, and if you try to change the aspect ratio of the slides it will diligently resize all images to that new aspect ratio.  It's terrible, but it worked.

We used the liner note boxes to build a fairly detailed outline of the talk — much more detailed than I would usually have for a talk.  The assumption was that the usual caveats about learning your speech by heart don't apply as strongly to a pre-recorded talk.  This ended up being useful in the captioning phase.

Step 2: Record the speech
=========================

I suppose you could do this at the same time as you're recording the slides, but it's 30°C in Boston right now and recording both my screen and my camera caused my 2014 laptop to overheat and lag.

For some reason VLC's latency is abominable with my webcam (> 1s), so I used `Guvcview <apt:giuvcview>`_ instead (packaged as ``guvcview`` in Ubuntu), which conveniently re-exposes most of the settings that are typically only accessible through |v4l2-ctl|_ (package ``v4l-utils``) or |qv4l2|_ (package ``v4l2ctl``).  (Ubuntu comes pre-packaged with `Cheese <apt:cheese>`_, but it doesn't give you quite control over the recording format.)

In practice, you don't need to record in HD, since you'll be embedding the camera image into your slides (in fact a properly stabilized phone would probably work just as well as a computer webcam).  I recommend 480x360.

If you want to post-process the audio to reduce noise, leave a few seconds at the beginning or at the end to recording a usable noise profile.

.. |v4l2-ctl| replace:: ``v4l2-ctl``
.. _v4l2-ctl: apt:v4l-utils

.. |qv4l2| replace:: ``qv4l2``
.. _qv4l2: apt:qv4l2

Step 3: Record the slides
=========================

I used `Simple screen recorder <apt:simplescreenrecorder>`_ (package ``simplescreenrecorder``), which is much more elaborate than the name suggests and works very nicely, to record my screen as I flipped through the slides.

The trick to align the slides and the webcam's audio is to listen to the webcam recording as you go through the slides and to start recording the slides at the same time as you start listening to the audio recording.

It helps to record the slides in the resolution you'll need them at, to avoid having to resize them (though if your conference is going to record a volunteer's screen playing a scaled version of your video in VLC and stream that to YouTube using Zoom, paying attention to pixel-perfection is likely a waste of time).  I recommend 1440x1080.

Unless your conference plans to do it, make sure to include your name and the title of your talk on all slides, not just on the title slide (people who connect in the middle of the stream will thank you, or at least I think they will, because we didn't do it, so I don't know for sure).  Slide numbers are nice too, though not as useful as in a physical conference.

If you plan to add captions, leave some space at the bottom of the slides (unless you plan to add your webcam stream to the side of the slides, in which case you'll have space on the side).

With Google Slides, recording to exactly the right dimensions was pretty easy, because opening the web developer tools (*right click → Inspect*) and resizing the browser window shows the exact pixel dimensions of the webpage area.

Step 4: Put everything together
===============================

I used FFmpeg and promised myself that if I ever get an academic job I'll hire a student to write to write a DSL for video manipulation that doesn't look like `FFmpeg's filter graph syntax <https://ffmpeg.org/ffmpeg-filters.html#Filtergraph-syntax-1>`_, until I realized that the :del:`Simpsons` *Racket folks* `already did it <https://lang.video/>`_, so our version will probably have to be a dependently typed DSL in Coq and no one will want to use it.

Here's how to do the editing with FFmpeg.  If you know the steps in Racket's ``#lang video`` please make a PR to this post; I'll offer you a beer emoji next time we're together in an online conference chatroom::

    ffmpeg -i slides.mkv -i webcam.mp4 -filter_complex "[0:v] pad=width=1920:height=1080:x=0:y=0:color=black [left]; [1:v] scale=480:360 [right]; [left][right] overlay=x=main_w-overlay_w:y=0 [out]" -map "[out]" -map 1:a:0 koika.mp4

The syntax of this monster, explained:

- First, pad the first video (source ``[0:v]``) to 1920x1080, the final dimensions of the video, adding a black background and placing the video to the left (``x=0:y=0``); name the result ``[left]``::

     [0:v] pad=width=1920:height=1080:x=0:y=0:color=black [left];

- Second, scale the webcam video to 480x360 (you might not need this if you recorded in that size to begin with); name the result ``[right]``::

     [1:v] scale=480:360 [right];

  If you need to crop the webcam video, use this instead::

     [1:v] crop=960:720, scale=480:360 [right];

- Finally, compose the two images, naming the result ``[out]``::

     [left][right] overlay=x=main_w-overlay_w:y=0 [out]

Step 5: Add captions
====================

This is really easy to do if you have a detailed outline, and people will thank you (this time I speak from experience).

- If you read your talk from a script, start from that.  I copied our presenter notes into Emacs and did a pass through the talk at 75% speed to turn that into a full transcript.

- Upload the video to `Youtube <studio.youtube.com>`_ (no need to publish it, just upload it).  If you have a transcript, go to *Subtitles* and `upload it <https://support.google.com/youtube/answer/2734796#upload>`_.

- Wait for Google's magical gremlins to automatically synchronize your transcript with the video.  If you didn't upload a transcript, you'll get auto-generated captions that will make you feel like you need to take remedial classes in English pronunciation by offering such gems as *Internet vedic biplane processing infinite stream of inputs and producing infinitestream about butts*, an interesting take on *Consider an arithmetic pipeline, processing an infinite stream of inputs and producing an infinite stream of outputs*.  Maybe it works better for native speakers.

- Download the generated captions.  As far as I can tell Google only offers SBV as a subtitle format, which isn't very well supported.  FFmpeg should support it, but when I tried to use it to convert YouTube's subtitle file to SRT it mangled all the timestamps, so I used the Javascript on `this website <https://dcmp.org/learn/532-converting-youtube-sbv-subtitles-to-subrip-srt-format>`_ instead.

- Use `Aegisub <apt:aegisub>`_ (package ``aegisub``, but you need to ``sudo add-apt-repository ppa:alex-p/aegisub``) to position the captions and format them.  We used a side-by-side style for our video (instead of picture-in-picture), so there was a nice amount of blank space under the webcam video that we could put the captions in.  I used the *style editor* feature to set large left and top margins to place the text in that space.  Save the result to SubStation Alpha (``.ass``) format.

- If needed, adjust the line breaks.  With captions :del:`cramped` *carefully positioned*  in a narrow band to the right, explicit linebreaks are essentially useless, so I removed them all by opening the caption file in Emacs.

- Use FFmpeg to burn the captions into the video, unless your conference lets you upload them separately: ``ffmpeg -i koika.mp4 -vf "ass=koika.ass" -c:a copy koika.cc.mp4`` (trivia: burnt-in captions are usually called *open* captions, not closed captions)

  You can also do everything in a single pass like this::

     ffmpeg -i slides.mkv -i webcam.mp4 -filter_complex "[0:v] pad=width=1920:height=1080:x=0:y=0:color=black [left]; [1:v] scale=480:360 [right]; [left][right] overlay=x=main_w-overlay_w:y=0 [out]; [out] ass=koika.ass [final]" -map "[final]" -map 1:a:0 koika.cc.mp4

`This government website <https://www.section508.gov/create/video-social>`_ has a lot of information and tips on making videos more accessible.

Other notes
===========

Cleaning up the audio with Audacity
-----------------------------------

My first audio take was about 50% voice and 50% loud fan noises from my computer, with a hint of trucks passing down the street (I had opened the window to try to cool down the computer), so I had to post-process the audio to get a decent recording, which was a decent occasion to learn two important lessons: 1. ice packs are not an efficient way to cool down an overheating laptop (I tried) and 2. `Audacity <apt:audacity>`_ (package ``audacity``) works pretty well for reducing noise [#]_.  Hopefully you'll need neither of those tips.

- Use ``ffmpeg -i webcam.mkv -vn -acodec copy koika.aac`` to extract the audio.
- To remove the background noise:
  - Open the audio file in Audacity
  - Select a few seconds of noise only, then click *Effect → Noise reduction* and in the window that opens click *Get Noise Profile*.  At this point Audacity has captured a noise profile, based on your selection.
  - Select the full track (``Ctrl+A``) and click *Effect → Noise reduction* again.  The defaults are fine in my experience, so click *Preview* and then *OK*
  - Use *File → Export → Export Audio…* to export the cleaned-up audio back to *MP4 (AAC)*.
- Use ``ffmpeg -i koika.mkv -i koika.wav -c:a copy -c:v copy -map 0:v:0 -map 1:a:0 koika-audacity.mkv`` to reassemble the video and the audio without recoding either.


.. [#] Apparently Audacity was started 20 years ago at CMU, roughly two years before I started middle school, which explains why it was exciting new tech back when I was in middle school.  The UI hasn't changed.  It works great.
